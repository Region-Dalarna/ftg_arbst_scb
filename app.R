library(shiny)
library(shinyjs)
library(shinyWidgets)
library(dplyr)
library(writexl)
library(readr)
library(DBI)
library(dbplyr)
library(sf)
library(future)
library(promises)
library(DT)

plan(multisession)

source("https://raw.githubusercontent.com/Region-Dalarna/funktioner/main/func_shinyappar.R")

`%||%` <- function(x, y) if (!is.null(x)) x else y

excel_max_rader <- 1048576L

# ── Kataloger ────────────────────────────────────────────────────────────────
# Absoluta sökvägar så att future-workers skriver till rätt plats oavsett
# arbetskatalog. www/nedladdning serveras statiskt av Shiny Server, dvs.
# filerna nås direkt via <app-url>/nedladdning/<fil>.

app_dir <- normalizePath(".", winslash = "/")

nedladdning_dir <- file.path(app_dir, "www", "nedladdning")

dir.create(nedladdning_dir, showWarnings = FALSE, recursive = TRUE)

# ── Hjälpfunktioner ─────────────────────────────────────────────────────────

filnamn_sakert <- function(x) {
  x |>
    as.character() |>
    gsub("å", "a", x = _, fixed = TRUE) |>
    gsub("ä", "a", x = _, fixed = TRUE) |>
    gsub("ö", "o", x = _, fixed = TRUE) |>
    gsub("Å", "A", x = _, fixed = TRUE) |>
    gsub("Ä", "A", x = _, fixed = TRUE) |>
    gsub("Ö", "O", x = _, fixed = TRUE) |>
    gsub("[^A-Za-z0-9_-]+", "_", x = _) |>
    gsub("_+", "_", x = _) |>
    gsub("^_|_$", "", x = _)
}

ta_bort_geometri <- function(df) {
  if (inherits(df, "sf")) {
    sf::st_drop_geometry(df)
  } else {
    df
  }
}

# ── Arbetsställen: platt SQL-resultat → sf vid gpkg-export ──────────────────
# arb_sql_bas_bygg() (nedan) frågar databasen med ST_X()/ST_Y() i stället
# för att returnera PostGIS-geometrikolumnen rakt av, så att tabellen och
# CSV/xlsx-exporterna alltid är vanliga platta data frames (enkla och
# snabba att serialisera/skriva). Geometrin återskapas bara i det enda
# steg som faktiskt behöver den: gpkg-nedladdningen.

arb_crs_epsg_standard <- 3006L  # SWEREF99 TM

arb_till_sf <- function(df) {
  if (inherits(df, "sf")) {
    return(df)
  }

  crs_epsg <- attr(df, "arb_crs_epsg", exact = TRUE) %||% arb_crs_epsg_standard

  if (is.na(crs_epsg)) {
    crs_epsg <- arb_crs_epsg_standard
  }

  sf::st_as_sf(
    df,
    coords = c("koordinat_ost", "koordinat_norr"),
    crs = crs_epsg,
    remove = TRUE
  )
}

geo_text <- function(geo_val, geo_df = NULL) {
  if (is.null(geo_val) || geo_val == "__ALL__") {
    return("Hela Sverige")
  }

  if (is.null(geo_df)) {
    return(geo_val)
  }

  if (startsWith(geo_val, "LAN::")) {
    vald_lanskod <- sub("^LAN::", "", geo_val)

    namn <- geo_df |>
      dplyr::filter(.data[["län, kod"]] == vald_lanskod) |>
      dplyr::distinct(.data[["län"]]) |>
      dplyr::pull(.data[["län"]])

    return(namn[[1]] %||% vald_lanskod)
  }

  if (startsWith(geo_val, "KOM::")) {
    vald_kommunkod <- sub("^KOM::", "", geo_val)

    namn <- geo_df |>
      dplyr::filter(.data[["kommun, kod"]] == vald_kommunkod) |>
      dplyr::distinct(.data[["kommun"]]) |>
      dplyr::pull(.data[["kommun"]])

    return(namn[[1]] %||% vald_kommunkod)
  }

  geo_val
}

ftg_where_sql <- function(con, geo_val) {
  if (is.null(geo_val) || geo_val == "__ALL__") {
    return("")
  }

  if (startsWith(geo_val, "LAN::")) {
    vald_lanskod <- sub("^LAN::", "", geo_val)

    return(
      paste0(
        " WHERE ",
        DBI::dbQuoteIdentifier(con, "säteslän, kod"),
        " = ",
        DBI::dbQuoteString(con, vald_lanskod)
      )
    )
  }

  if (startsWith(geo_val, "KOM::")) {
    vald_kommunkod <- sub("^KOM::", "", geo_val)

    return(
      paste0(
        " WHERE ",
        DBI::dbQuoteIdentifier(con, "säteskommun, kod"),
        " = ",
        DBI::dbQuoteString(con, vald_kommunkod)
      )
    )
  }

  ""
}

arb_where_sql <- function(con, geo_val) {
  if (is.null(geo_val) || geo_val == "__ALL__") {
    return("")
  }

  if (startsWith(geo_val, "LAN::")) {
    vald_lanskod <- sub("^LAN::", "", geo_val)

    return(
      paste0(
        " WHERE ",
        DBI::dbQuoteIdentifier(con, "län, kod"),
        " = ",
        DBI::dbQuoteString(con, vald_lanskod)
      )
    )
  }

  if (startsWith(geo_val, "KOM::")) {
    vald_kommunkod <- sub("^KOM::", "", geo_val)

    return(
      paste0(
        " WHERE ",
        DBI::dbQuoteIdentifier(con, "kommun, kod"),
        " = ",
        DBI::dbQuoteString(con, vald_kommunkod)
      )
    )
  }

  ""
}

# ── SQL-baserad tabellvisning: kolumninfo och arbetsställenas platta bas ────
# Tabellen och exporterna frågar nu databasen direkt i stället för att
# hålla hela datasetet i R-minnet. Två saker cachas processgemensamt
# (delad_data) eftersom de är dyra att räkna ut men i praktiken statiska:
# kolumnernas namn/typer (numerisk vs text, avgör ILIKE vs BETWEEN) och,
# för arbetsställen, vilken kolumn som är geometrin.
#
# OBS – detta bygger på ett par antaganden om databasschemat som INTE är
# verifierade mot en riktig körning:
#  1. Att malpunkter.arbetsstallen har exakt en PostGIS-geometrikolumn,
#     hittad via information_schema.columns (udt_name = 'geometry').
#  2. Att geometrins SRID är SWEREF99 TM (EPSG:3006) – samma antagande som
#     redan gjordes i arb_till_sf()/arb_crs_epsg_standard.
# Om något av detta inte stämmer syns det direkt som ett fel eller
# uppenbart galna koordinater vid första testkörningen – hör av dig så
# justerar jag.

arb_geometrikolumn_hamta <- function(con) {
  info <- DBI::dbGetQuery(
    con,
    "
    SELECT column_name
    FROM information_schema.columns
    WHERE table_schema = 'malpunkter'
      AND table_name = 'arbetsstallen'
      AND udt_name = 'geometry'
    "
  )

  if (nrow(info) == 0) {
    return(NULL)
  }

  info$column_name[[1]]
}

arb_sql_bas_bygg <- function(con) {
  geom_kol <- arb_geometrikolumn_hamta(con)

  if (is.null(geom_kol)) {
    warning(
      "Hittade ingen geometrikolumn i malpunkter.arbetsstallen ",
      "(letade efter udt_name = 'geometry') – tabellen visas utan ",
      "koordinatkolumner. Kontrollera kolumnnamnet manuellt om detta är ",
      "fel."
    )
    return("SELECT * FROM malpunkter.arbetsstallen")
  }

  alla_kolumner <- DBI::dbGetQuery(
    con,
    "
    SELECT column_name
    FROM information_schema.columns
    WHERE table_schema = 'malpunkter'
      AND table_name = 'arbetsstallen'
    ORDER BY ordinal_position
    "
  )$column_name

  ovriga <- setdiff(alla_kolumner, geom_kol)
  select_lista <- paste(DBI::dbQuoteIdentifier(con, ovriga), collapse = ", ")
  geom_sql <- DBI::dbQuoteIdentifier(con, geom_kol)

  paste0(
    "SELECT ", select_lista, ", ",
    "ST_X(", geom_sql, ") AS koordinat_ost, ",
    "ST_Y(", geom_sql, ") AS koordinat_norr ",
    "FROM malpunkter.arbetsstallen"
  )
}

arb_sql_bas_cache <- function(con_fun) {
  cached <- delad_data[["arb_sql_bas"]]

  if (!is.null(cached)) {
    return(cached)
  }

  con <- con_fun()
  on.exit(DBI::dbDisconnect(con), add = TRUE)

  sql_bas <- arb_sql_bas_bygg(con)
  delad_data[["arb_sql_bas"]] <- sql_bas

  sql_bas
}

sql_kolumninfo <- function(con, sql_bas) {
  df <- DBI::dbGetQuery(con, paste0(sql_bas, " LIMIT 1"))

  namn <- names(df)
  ar_numerisk <- vapply(df, is.numeric, logical(1))

  # DT inaktiverar (grayar ut) ett kolumnfilter om den data den FÅR SE inte
  # ger den något att arbeta med: för sifferkolumner krävs max > min för att
  # slidern inte ska bli disabled (se DT::columnFilters() – "disabled =
  # !(is.finite(d1) && is.finite(d2) && d2 > d1)"). Eftersom tabellens
  # riktiga data aldrig hålls i R-minnet (databasdriven arkitektur) måste
  # vi hämta den riktiga min/max separat, en gång, och återanvända den som
  # platshållardata när widgeten byggs – annars blir varje sifferfilter
  # låst precis som textfälten var.
  min_varde <- rep(NA_real_, length(namn))
  max_varde <- rep(NA_real_, length(namn))

  if (any(ar_numerisk)) {
    num_namn <- namn[ar_numerisk]

    minmax_sql <- paste(
      vapply(num_namn, function(n) {
        id <- DBI::dbQuoteIdentifier(con, n)
        paste0("MIN(", id, ") AS ", DBI::dbQuoteIdentifier(con, paste0(n, "__min")),
               ", MAX(", id, ") AS ", DBI::dbQuoteIdentifier(con, paste0(n, "__max")))
      }, character(1)),
      collapse = ", "
    )

    minmax_df <- tryCatch(
      DBI::dbGetQuery(con, paste0("SELECT ", minmax_sql, " FROM (", sql_bas, ") _bas")),
      error = function(e) {
        warning(paste0("Kunde inte hämta min/max för numeriska kolumner: ", conditionMessage(e)))
        NULL
      }
    )

    if (!is.null(minmax_df) && nrow(minmax_df) == 1) {
      for (n in num_namn) {
        idx <- match(n, namn)
        min_varde[idx] <- suppressWarnings(as.numeric(minmax_df[[paste0(n, "__min")]][[1]]))
        max_varde[idx] <- suppressWarnings(as.numeric(minmax_df[[paste0(n, "__max")]][[1]]))
      }
    }
  }

  data.frame(
    name = namn,
    ar_numerisk = ar_numerisk,
    min_varde = min_varde,
    max_varde = max_varde,
    stringsAsFactors = FALSE
  )
}

kolumninfo_cache <- function(key, con_fun, sql_bas) {
  cached <- delad_data[[key]]

  if (!is.null(cached)) {
    return(cached)
  }

  con <- con_fun()
  on.exit(DBI::dbDisconnect(con), add = TRUE)

  info <- sql_kolumninfo(con, sql_bas)
  delad_data[[key]] <- info

  info
}

# ── DT server-side-processing direkt mot databasen ──────────────────────────
# Bygger DataTables' förväntade svarsformat (draw/recordsTotal/
# recordsFiltered/data) från en enda SQL-fråga per sida, i stället för att
# ladda hela datasetet i R-minnet. Kopplas in via session$registerDataObj()
# med en egen filterfunktion (se registrera_dt_kalla()), vilket är DT:s
# dokumenterade väg för en helt egen databaskälla – ANVÄNDS FÖR FÖRSTA
# GÅNGEN HÄR och är inte testad mot en riktig Shiny-session/databas.

bygg_dt_svar <- function(con, sql_bas, kolumn_info, geo_where, req_params, extra_order_by = NULL) {
  kolumner <- kolumn_info$name

  # shiny::parseQueryString(..., nested = TRUE) bygger en riktig nästlad
  # lista av DataTables bracket-notation ("columns[0][search][value]"
  # blir req_params$columns[[1]]$search$value), INTE platta strängnycklar.
  # Bekräftat mot DT:s egen referensimplementation (dataTablesFilter i
  # DT:s källkod använder exakt samma struktur: q$columns[[j]][['search']]
  # osv.). Tidigare version av den här funktionen läste platta nycklar som
  # aldrig fanns, så alla filter/sortering ignorerades tyst.
  kolumn_param <- function(i) {
    tryCatch(req_params$columns[[i]], error = function(e) NULL)
  }

  sok_per_kolumn <- vapply(
    seq_along(kolumner),
    function(i) {
      kp <- kolumn_param(i)
      v <- if (!is.null(kp)) kp$search$value else NULL
      if (is.null(v)) "" else v
    },
    character(1)
  )

  villkor <- sql_villkor_kombinera(con, geo_where, sok_per_kolumn, kolumn_info)
  where_sql <- sql_where_sats(villkor)
  geo_villkor <- sql_villkor_kombinera(con, geo_where, NULL, kolumn_info)
  geo_where_sql <- sql_where_sats(geo_villkor)

  order_post <- tryCatch(req_params$order[[1]], error = function(e) NULL)
  order_col_idx <- if (!is.null(order_post)) order_post$column else NULL
  order_dir <- if (!is.null(order_post)) order_post$dir else NULL

  order_sql <- ""

  if (!is.null(order_col_idx)) {
    idx <- suppressWarnings(as.integer(order_col_idx)) + 1L

    if (!is.na(idx) && idx >= 1 && idx <= length(kolumner)) {
      riktning <- if (identical(order_dir, "desc")) "DESC" else "ASC"
      order_sql <- paste0(
        " ORDER BY ", DBI::dbQuoteIdentifier(con, kolumner[idx]), " ", riktning
      )
    }
  }

  if (!nzchar(order_sql) && !is.null(extra_order_by)) {
    order_sql <- paste0(" ORDER BY ", extra_order_by)
  }

  # start/length/draw skickas som platta toppnivåfält (inga hakparenteser),
  # så de påverkas inte av nested = TRUE och läses precis som förut.
  start_ <- suppressWarnings(as.integer(req_params[["start"]] %||% "0"))
  if (is.na(start_) || start_ < 0) start_ <- 0L

  length_ <- suppressWarnings(as.integer(req_params[["length"]] %||% "25"))
  if (is.na(length_) || length_ < 0) length_ <- 25L

  data_df <- DBI::dbGetQuery(
    con,
    paste0(
      "SELECT * FROM (", sql_bas, ") _bas",
      where_sql, order_sql,
      " LIMIT ", length_, " OFFSET ", start_
    )
  )

  antal_filtrerat <- DBI::dbGetQuery(
    con,
    paste0("SELECT COUNT(*) AS n FROM (", sql_bas, ") _bas", where_sql)
  )$n[[1]]

  antal_totalt <- DBI::dbGetQuery(
    con,
    paste0("SELECT COUNT(*) AS n FROM (", sql_bas, ") _bas", geo_where_sql)
  )$n[[1]]

  list(
    draw = suppressWarnings(as.integer(req_params[["draw"]] %||% "1")),
    recordsTotal = antal_totalt,
    recordsFiltered = antal_filtrerat,
    data = unname(lapply(
      seq_len(nrow(data_df)),
      function(i) unname(as.list(data_df[i, , drop = FALSE]))
    ))
  )
}

registrera_dt_kalla <- function(session, output_id, con_fun, sql_bas, kolumn_info,
                                geo_where_fn, extra_order_by = NULL) {
  # Paketerar en R-lista som ett riktigt HTTP-svar. session$registerDataObj()
  # kräver ett komplett svarsobjekt (status/headers/body) – returnerar man
  # bara den råa listan (som tidigare) kraschar Shinys interna hantering med
  # "Index out of bounds: [index='status']" eftersom den letar efter ett
  # status-fält som inte finns. Detta är exakt vad DT:s egen inbyggda
  # sessionDataURL() gör internt (bekräftat mot DT:s källkod).
  json_svar <- function(res) {
    json_txt <- jsonlite::toJSON(
      res,
      dataframe = "rows",
      auto_unbox = TRUE,
      na = "null",
      null = "null"
    )

    shiny::httpResponse(200L, "application/json", enc2utf8(json_txt))
  }

  filter_fn <- function(data, req) {
    # DataTables server-side-läge skickar sina parametrar som POST (kroppen),
    # inte som query-sträng – annars blir GET-URL:en orimligt lång med många
    # kolumner (varje kolumn skickar data/name/searchable/orderable/sök-
    # värde). req$QUERY_STRING är därför fel ställe att läsa; kroppen läses
    # via req$rook.input$read(), exakt som DT:s egen implementation gör.
    kropp <- tryCatch(
      rawToChar(req$rook.input$read()),
      error = function(e) ""
    )
    Encoding(kropp) <- "UTF-8"

    req_params <- shiny::parseQueryString(kropp, nested = TRUE)

    con <- tryCatch(con_fun(), error = function(e) NULL)

    if (is.null(con)) {
      if (!session$isClosed()) {
        shiny::showNotification(
          "Kunde inte ansluta till databasen. Kontrollera anslutningen och prova igen.",
          id = "dt_db_fel", duration = 8, type = "error", session = session
        )
      }
      return(json_svar(list(draw = 1L, recordsTotal = 0, recordsFiltered = 0, data = list())))
    }

    on.exit(DBI::dbDisconnect(con), add = TRUE)

    res <- tryCatch(
      bygg_dt_svar(
        con, sql_bas, kolumn_info, geo_where_fn(con), req_params, extra_order_by
      ),
      error = function(e) {
        warning(paste0("DT-tabellfråga misslyckades: ", conditionMessage(e)))

        if (!session$isClosed()) {
          shiny::showNotification(
            paste0("Tabellfrågan mot databasen misslyckades (", conditionMessage(e), ")."),
            id = "dt_db_fel", duration = 8, type = "error", session = session
          )
        }

        list(draw = 1L, recordsTotal = 0, recordsFiltered = 0, data = list())
      }
    )

    json_svar(res)
  }

  session$registerDataObj(output_id, data = NULL, filter_fn)
}

# ── Filtrerad export (nedladdningsknappar) ──────────────────────────────────
# Samma villkorsbyggare som tabellen, men utan sidvisning – hämtar hela den
# filtrerade träffmängden för nedladdning. sok_kolumner kommer från
# input$preview_search_columns (se JS i output$preview) och är i samma
# ordning som kolumn_info$name.

hamta_antal_sql <- function(con_fun, sql_bas, geo_where_fn, sok_kolumner, kolumn_info) {
  con <- con_fun()
  on.exit(DBI::dbDisconnect(con), add = TRUE)

  geo_where <- geo_where_fn(con)

  totalt <- DBI::dbGetQuery(
    con,
    paste0(
      "SELECT COUNT(*) AS n FROM (", sql_bas, ") _bas",
      sql_where_sats(sql_villkor_kombinera(con, geo_where, NULL, kolumn_info))
    )
  )$n[[1]]

  filtrerat <- DBI::dbGetQuery(
    con,
    paste0(
      "SELECT COUNT(*) AS n FROM (", sql_bas, ") _bas",
      sql_where_sats(sql_villkor_kombinera(con, geo_where, sok_kolumner, kolumn_info))
    )
  )$n[[1]]

  list(totalt = totalt, filtrerat = filtrerat)
}

hamta_filtrerat_export <- function(con_fun, sql_bas, geo_where_fn, sok_kolumner, kolumn_info) {
  con <- con_fun()
  on.exit(DBI::dbDisconnect(con), add = TRUE)

  geo_where <- geo_where_fn(con)
  where_sql <- sql_where_sats(
    sql_villkor_kombinera(con, geo_where, sok_kolumner, kolumn_info)
  )

  DBI::dbGetQuery(con, paste0("SELECT * FROM (", sql_bas, ") _bas", where_sql))
}

skriv_tabell_excel_eller_zip <- function(df, file, basnamn) {
  df <- ta_bort_geometri(df)

  if (nrow(df) <= excel_max_rader) {
    writexl::write_xlsx(df, path = file)
  } else {
    tmp_dir <- tempfile("export_")
    dir.create(tmp_dir, recursive = TRUE)

    csv_fil <- file.path(tmp_dir, paste0(basnamn, ".csv"))
    readme_fil <- file.path(tmp_dir, "README.txt")

    readr::write_excel_csv2(df, csv_fil, na = "")

    writeLines(
      c(
        "Datasetet är större än vad en Excel-flik kan hantera.",
        "Därför exporteras data som CSV i en ZIP-fil.",
        "",
        "Tips:",
        "- Öppna CSV-filen i Excel via Data > Från text/CSV.",
        "- CSV-filen är semikolonseparerad och anpassad för svensk Excel.",
        paste0("Antal rader: ", nrow(df)),
        paste0("Exporterad: ", Sys.Date())
      ),
      readme_fil,
      useBytes = TRUE
    )

    old_wd <- getwd()
    on.exit(setwd(old_wd), add = TRUE)

    setwd(tmp_dir)

    utils::zip(
      zipfile = file,
      files = c(basename(csv_fil), basename(readme_fil)),
      flags = "-q"
    )
  }
}

# ── Processgemensam cache (kolumninfo, SQL-bas) ─────────────────────────────
# Shiny Server kör alla sessioner av appen i samma R-process. Miljön här
# används av kolumninfo_cache()/arb_sql_bas_cache() nedan för att slippa
# göra samma information_schema-frågor för varje session.

delad_data <- new.env(parent = emptyenv())

# ── Statisk zip-fil i www/nedladdning ───────────────────────────────────────
# Hela dataseten (ofiltrerade, samtliga kolumner) byggs INTE längre av
# appen – de skrivs av ett fristående cron-skript (se
# cron_bygg_nedladdningszip.R) helt frikopplat från Shiny-processen.
# Appen känner bara av om filen finns och visar en länk + filstorlek.

zip_fil <- function(namn) {
  file.path(nedladdning_dir, paste0(namn, ".zip"))
}

filstorlek_text <- function(fil) {
  format(
    structure(file.size(fil), class = "object_size"),
    units = "auto",
    standard = "SI"
  )
}

# ── Kolumnfilter → SQL ───────────────────────────────────────────────────────
# Översätter DT:s per-kolumn sökvärden till SQL-villkor, så att filtrering,
# sidvisning och export sker i databasen i stället för i R-minnet. Hanterar
# textsökning (ILIKE) och numeriska intervall i samma format som DT:s
# inbyggda filter skickar ("3 ... 7").

sql_kolumnvillkor <- function(con, kolumn_namn, sok, ar_numerisk) {
  sok <- trimws(as.character(sok %||% ""))

  if (!nzchar(sok)) {
    return(NULL)
  }

  kol_sql <- DBI::dbQuoteIdentifier(con, kolumn_namn)

  if (isTRUE(ar_numerisk)) {
    m <- regmatches(
      sok,
      regexec("^(-?[0-9.]+)\\s*\\.\\.\\.\\s*(-?[0-9.]+)$", sok)
    )[[1]]

    if (length(m) == 3) {
      return(paste0(
        kol_sql, " BETWEEN ", as.numeric(m[2]), " AND ", as.numeric(m[3])
      ))
    }

    if (grepl("^-?[0-9.]+$", sok)) {
      return(paste0(kol_sql, " = ", as.numeric(sok)))
    }

    # Okänt/ogiltigt format för en numerisk kolumn – hellre ignorera
    # filtret än att skicka trasig SQL till databasen.
    return(NULL)
  }

  # Enkel textsökning. Escapa SQL LIKE-jokertecken i användarens text
  # innan de omges av egna %-tecken.
  sok_escaped <- gsub("([%_\\\\])", "\\\\\\1", sok)

  paste0(
    kol_sql, " ILIKE ",
    DBI::dbQuoteString(con, paste0("%", sok_escaped, "%")),
    " ESCAPE '\\'"
  )
}

kolumnfilter_aktivt <- function(sok_kolumner) {
  !is.null(sok_kolumner) && any(nzchar(sok_kolumner), na.rm = TRUE)
}

# Bygger en komplett WHERE-sats (utan "WHERE") av geo-villkor + aktiva
# kolumnfilter. geo_where kommer från ftg_where_sql()/arb_where_sql() och
# har formen " WHERE ..." eller "".
sql_villkor_kombinera <- function(con, geo_where, sok_kolumner, kolumn_info) {
  villkor <- character(0)

  if (!is.null(sok_kolumner)) {
    n <- min(length(sok_kolumner), nrow(kolumn_info))

    if (n > 0) {
      for (i in seq_len(n)) {
        v <- sql_kolumnvillkor(
          con, kolumn_info$name[i], sok_kolumner[[i]], kolumn_info$ar_numerisk[i]
        )

        if (!is.null(v)) {
          villkor <- c(villkor, v)
        }
      }
    }
  }

  geo_del <- if (nzchar(geo_where)) sub("^\\s*WHERE\\s*", "", geo_where) else NULL

  c(geo_del, villkor)
}

sql_where_sats <- function(villkor_lista) {
  if (length(villkor_lista) == 0) {
    return("")
  }

  paste0(" WHERE ", paste(villkor_lista, collapse = " AND "))
}

hamta_version_ftg <- function() {
  con <- shiny_uppkoppling_las("oppna_data")
  on.exit(DBI::dbDisconnect(con), add = TRUE)

  DBI::dbGetQuery(
    con,
    "
    SELECT version_datum
    FROM metadata.aktuell_version
    WHERE schema = 'scb'
      AND tabell = 'foretag'
    LIMIT 1
    "
  )$version_datum[[1]]
}

hamta_version_arb <- function() {
  con <- shiny_uppkoppling_las("geodata")
  on.exit(DBI::dbDisconnect(con), add = TRUE)

  DBI::dbGetQuery(
    con,
    "
    SELECT version_datum
    FROM metadata.aktuell_version
    WHERE schema = 'malpunkter'
      AND tabell = 'arbetsstallen'
    LIMIT 1
    "
  )$version_datum[[1]]
}

# Säker version av ovanstående: fångar både anslutnings-/SQL-fel och
# fallet att frågan lyckas men inte ger någon träff (t.ex. saknad rad i
# metadata.aktuell_version). I båda fallen kastar `$version_datum[[1]]`
# annars "subscript out of bounds", vilket stoppar den observer som
# anropar den – och eftersom HELA kedjan (databashämtning, inläsning,
# zip-byggande) väntar på ett icke-NULL versionsvärde fryser den delen
# av appen helt tyst. Reservvärdet Sys.Date() gör att appen ändå fungerar
# (cachen räknas som aktuell resten av dagen, byggs om en gång per dag),
# men den riktiga fixen är att se till att metadatatabellen har en rad
# för respektive schema/tabell.
hamta_version_sakert <- function(hamta_funktion, namn) {
  ver <- tryCatch(
    hamta_funktion(),
    error = function(e) {
      warning(
        paste0(
          "Kunde inte hämta version för ", namn, ": ", conditionMessage(e),
          " – använder dagens datum som reservversion."
        )
      )
      NULL
    }
  )

  if (is.null(ver) || length(ver) == 0 || is.na(ver)) {
    warning(
      paste0(
        "Ingen version hittades för ", namn,
        " i metadata.aktuell_version – använder dagens datum som ",
        "reservversion."
      )
    )
    return(as.character(Sys.Date()))
  }

  ver
}

# ── UI ──────────────────────────────────────────────────────────────────────

ui <- fluidPage(
  shinyjs::useShinyjs(),

  tags$head(
    tags$link(rel = "icon", type = "image/x-icon", href = "favicon.ico"),
    tags$link(rel = "stylesheet", type = "text/css", href = "regiondalarna_ruf.css"),
    tags$link(rel = "stylesheet", type = "text/css", href = "app.css")
  ),

  tags$div(
    class = "rd-header",
    tags$div(
      class = "rd-header__title",
      "Företag och arbetsställen i Sverige"
    ),
    tags$a(
      class  = "rd-header__right",
      href   = "https://www.regiondalarna.se",
      target = "_blank",
      tags$img(src = "logo_liggande_fri_vit.png", alt = "Region Dalarna"),
      tags$span("Samhällsanalys")
    )
  ),

  div(
    class = "rd-compact-page",

    div(
      class = "rd-card rd-controls-compact",

      fluidRow(
        column(
          width = 4,
          div(
            class = "rd-field",
            shinyWidgets::pickerInput(
              inputId = "geo_val",
              label = "Län och kommuner",
              choices = c("Hela Sverige" = "__ALL__"),
              selected = "__ALL__",
              options = shinyWidgets::pickerOptions(
                liveSearch = TRUE,
                noneSelectedText = "Välj område"
              )
            )
          )
        ),

        column(
          width = 3,
          div(
            class = "rd-field",
            radioButtons(
              inputId  = "visa",
              label    = "Visa och filtrera",
              choices  = c("Företag" = "ftg", "Arbetsställen" = "arb"),
              selected = "ftg",
              inline   = TRUE
            )
          )
        ),

        column(
          width = 5,
          div(
            class = "rd-download-grid",

            div(
              class = "rd-download-cell",
              tags$span(
                title = "Laddar ned det du ser i tabellen: valt område och aktiva kolumnfilter. Excel när uttaget ryms i en Excel-flik, annars CSV i ZIP.",
                downloadButton(
                  "ladda_ned_ftg",
                  "Företag",
                  class = "rd-btn rd-btn--primary"
                )
              ),
              uiOutput("direktlank_ftg", inline = TRUE)
            ),

            div(
              class = "rd-download-cell",
              tags$span(
                title = "Laddar ned det du ser i tabellen: valt område och aktiva kolumnfilter. Excel när uttaget ryms i en Excel-flik, annars CSV i ZIP.",
                downloadButton(
                  "ladda_ned_arb",
                  "Arbetsställen",
                  class = "rd-btn rd-btn--primary"
                )
              ),
              uiOutput("direktlank_arb", inline = TRUE)
            ),

            div(
              class = "rd-download-cell",
              tags$span(
                title = "Geopackage med arbetsställen och geometri. Följer valt område och aktiva kolumnfilter.",
                downloadButton(
                  "ladda_ned_arb_gpkg",
                  ".gpkg",
                  class = "rd-btn rd-btn--ghost"
                )
              )
            )
          )
        )
      )
    ),

    div(
      class = "rd-card rd-table-card rd-table-fill",
      div(
        class = "rd-preview-meta",
        h2(textOutput("preview_rubrik")),
        span(class = "rd-uppdaterad", textOutput("uppdaterad_text", inline = TRUE)),
        span(textOutput("export_info_text", inline = TRUE)),
        span(
          class = "rd-filterhint",
          "Filtrera i fälten under kolumnrubrikerna – filtren följer med i nedladdningarna."
        )
      ),

      DT::DTOutput("preview")
    )
  ),

  tags$div(
    class = "rd-footer",
    "Samhällsanalys, Region Dalarna · ",
    tags$a(
      href = "mailto:samhallsanalys@regiondalarna.se",
      "samhallsanalys@regiondalarna.se"
    )
  )
)

# ── Server ──────────────────────────────────────────────────────────────────

server <- function(input, output, session) {

  # ── Notiser med explicit session ──────────────────────────────────────────
  # shiny::showNotification() hämtar sessionen implicit via
  # getDefaultReactiveDomain(). I callbacks från future/promises (t.ex.
  # onFulfilled/onRejected) finns ingen sådan domän – session blir NULL
  # och anropet kraschar med "attempt to apply non-function". Sessions-
  # objektet fångas därför i closuren och skickas alltid explicit; notiser
  # till stängda sessioner ignoreras tyst.
  notis_visa <- function(...) {
    if (!session$isClosed()) {
      shiny::showNotification(..., session = session)
    }

    invisible()
  }

  notis_bort <- function(id) {
    if (!session$isClosed()) {
      shiny::removeNotification(id, session = session)
    }

    invisible()
  }

  geo_lookup <- reactiveVal(NULL)

  uppdaterad_arbst <- reactiveVal(NULL)
  uppdaterad_ftg <- reactiveVal(NULL)

  # Innan pickern hunnit uppdateras (kräver en rundresa till klienten) är
  # input$geo_val NULL – behandla det som "Sverige" så att tabellen kan
  # renderas redan i första flushen.
  geo_vald <- reactive(input$geo_val %||% "__ALL__")

  # ── Hämta geografilista ───────────────────────────────────────────────────
  # DISTINCT-frågan går över hela arbetsställetabellen och kan ta lång tid.
  # Den körs därför i en bakgrundsworker. Pickern har "Sverige" som startval
  # så tabellen kan renderas direkt; län/kommuner fylls på när frågan är klar.

  observeEvent(TRUE, {
    future_promise({
      con <- shiny_uppkoppling_las("geodata")
      on.exit(DBI::dbDisconnect(con), add = TRUE)

      DBI::dbGetQuery(
        con,
        '
        SELECT DISTINCT
          "kommun, kod",
          "kommun",
          "län, kod",
          "län"
        FROM malpunkter.arbetsstallen
        WHERE "kommun" IS NOT NULL
        ORDER BY "län", "kommun"
        '
      )
    }) |>
      promises::then(
        onFulfilled = function(geo_df) {
          geo_lookup(geo_df)
        },
        onRejected = function(e) {
          warning(conditionMessage(e))
          notis_visa(
            paste0("Kunde inte hämta listan över län/kommuner (", conditionMessage(e), ")."),
            duration = 8,
            type = "error"
          )
        }
      )

    # Fire and forget: returnera INTE promisen, annars håller Shiny alla
    # sessionens outputs tills bakgrundsjobbet är klart.
    invisible(NULL)
  }, once = TRUE)

  observeEvent(geo_lookup(), {
    geo_df <- geo_lookup()
    req(geo_df)

    sverige_val <- c("Hela Sverige" = "__ALL__")

    lan_df <- geo_df |>
      dplyr::filter(
        !is.na(.data[["län, kod"]]),
        !is.na(.data[["län"]]),
        .data[["län"]] != ""
      ) |>
      dplyr::distinct(.data[["län, kod"]], .data[["län"]]) |>
      dplyr::arrange(.data[["län"]])

    lan_val <- stats::setNames(
      paste0("LAN::", lan_df[["län, kod"]]),
      lan_df[["län"]]
    )

    kommun_df <- geo_df |>
      dplyr::filter(
        !is.na(.data[["kommun, kod"]]),
        !is.na(.data[["kommun"]]),
        .data[["kommun"]] != ""
      ) |>
      dplyr::distinct(.data[["kommun, kod"]], .data[["kommun"]]) |>
      dplyr::arrange(.data[["kommun"]])

    kommun_val <- stats::setNames(
      paste0("KOM::", kommun_df[["kommun, kod"]]),
      kommun_df[["kommun"]]
    )

    choices <- list(
      "Hela Sverige" = sverige_val,
      "Län" = lan_val,
      "Kommuner" = kommun_val
    )

    shinyWidgets::updatePickerInput(
      session = session,
      inputId = "geo_val",
      choices = choices,
      selected = "__ALL__"
    )
  })

  # ── Metadata (endast för "Senast uppdaterad"-visning) ────────────────────
  # Ingen cache-logik hänger längre på det här värdet – databasen är alltid
  # den levande källan. Hämtas asynkront (fire and forget) så att det inte
  # fördröjer sessionsstarten.

  observeEvent(TRUE, {
    future_promise({
      hamta_version_sakert(hamta_version_ftg, "företag")
    }) |>
      promises::then(
        onFulfilled = function(ver) uppdaterad_ftg(ver),
        onRejected = function(e) warning(conditionMessage(e))
      )

    invisible(NULL)
  }, once = TRUE)

  observeEvent(TRUE, {
    future_promise({
      hamta_version_sakert(hamta_version_arb, "arbetsställen")
    }) |>
      promises::then(
        onFulfilled = function(ver) uppdaterad_arbst(ver),
        onRejected = function(e) warning(conditionMessage(e))
      )

    invisible(NULL)
  }, once = TRUE)

  # ── Tabell och export: SQL direkt mot databasen ──────────────────────────
  # Tabellen håller INTE hela datasetet i R-minnet. Varje sidbyte, sortering
  # och kolumnfilter blir en egen SQL-fråga (LIMIT/OFFSET/WHERE), kopplad in
  # via session$registerDataObj() – se registrera_dt_kalla(). Det gör att
  # tabellen visar riktiga data på under en sekund oavsett datasetets
  # storlek, utan någon minnescache av hela datasetet. Kolumnfiltrens
  # sökvärden speglas till input$preview_search_columns via JS i callbacken
  # nedan, så att nedladdningsknapparna kan bygga samma SQL-villkor som
  # tabellen visar. De statiska "hela datasetet"-ziparna byggs separat av
  # ett fristående cron-skript (cron_bygg_nedladdningszip.R) – appen bara
  # länkar till dem om filerna finns, se direktlank_ui() nedan.

  ftg_con_fun <- function() shiny_uppkoppling_las("oppna_data")
  arb_con_fun <- function() shiny_uppkoppling_las("geodata")

  ftg_sql_bas <- "SELECT * FROM scb.foretag"

  arb_sql_bas <- reactive({
    arb_sql_bas_cache(arb_con_fun)
  })

  aktuell_kalla <- reactive({
    if (identical(input$visa, "ftg")) {
      list(
        con_fun = ftg_con_fun,
        sql_bas = ftg_sql_bas,
        # OBS: isolate() är nödvändigt här, inte kosmetiskt. geo_where_fn
        # sparas undan och anropas senare inifrån filter_fn i
        # registrera_dt_kalla() – en rå HTTP-anropad funktion utanför
        # Shinys reaktiva flush. Att anropa en reactive() (geo_vald())
        # därifrån utan isolate() ger "Operation not allowed without an
        # active reactive context" och kraschar VARJE tabellförfrågan.
        geo_where_fn = function(con) ftg_where_sql(con, isolate(geo_vald())),
        kolumn_info_key = "kolumner_foretag"
      )
    } else {
      list(
        con_fun = arb_con_fun,
        sql_bas = arb_sql_bas(),
        geo_where_fn = function(con) arb_where_sql(con, isolate(geo_vald())),
        kolumn_info_key = "kolumner_arbetsstallen"
      )
    }
  })

  output$preview_rubrik <- renderText({
    geo <- geo_text(geo_vald(), geo_lookup())

    if (input$visa == "ftg") {
      paste0("Företag, ", geo)
    } else {
      paste0("Arbetsställen, ", geo)
    }
  })

  output$uppdaterad_text <- renderText({
    if (input$visa == "ftg") {
      paste0("Senast uppdaterad: ", uppdaterad_ftg() %||% "uppgift saknas")
    } else {
      paste0("Senast uppdaterad: ", uppdaterad_arbst() %||% "uppgift saknas")
    }
  })

  # ── Tabell ──────────────────────────────────────────────────────────────
  # server = FALSE i renderDT() är medvetet: options$serverSide = TRUE +
  # options$ajax$url pekar på vår EGNA datakälla (registrera_dt_kalla),
  # så DT/Shiny ska inte samtidigt försöka registrera sin egen
  # default-hanterare för in-memory-filtrering.

  output$preview <- DT::renderDT({
    kalla <- aktuell_kalla()
    req(kalla$sql_bas)

    kolumn_info <- kolumninfo_cache(
      kalla$kolumn_info_key, kalla$con_fun, kalla$sql_bas
    )

    ajax_url <- registrera_dt_kalla(
      session = session,
      output_id = "preview",
      con_fun = kalla$con_fun,
      sql_bas = kalla$sql_bas,
      kolumn_info = kolumn_info,
      geo_where_fn = kalla$geo_where_fn
    )

    # VIKTIGT: platshallare måste ha minst två SKILDA värden per kolumn.
    # DT:s columnFilters() inaktiverar (grayar ut, olåsbart) ett kolumn-
    # filter om den data den ser inte räcker för att avgöra en meningsfull
    # widget: textkolumner kräver > 1 unikt värde, sifferkolumner kräver
    # max > min. Med noll rader (som tidigare) blev ALLA filter låsta –
    # det var precis det du såg. Sifferkolumner får sitt RIKTIGA min/max
    # (för en korrekt skalad slider); textkolumner får två godtyckliga
    # dummyvärden (de visas aldrig – DT bygger ingen nedladdningslista av
    # textkolumner, bara ett vanligt sökfält, så innehållet spelar ingen
    # roll, bara att det är två olika strängar).
    platshallare <- as.data.frame(
      stats::setNames(
        lapply(seq_len(nrow(kolumn_info)), function(i) {
          if (isTRUE(kolumn_info$ar_numerisk[i]) &&
              is.finite(kolumn_info$min_varde[i]) &&
              is.finite(kolumn_info$max_varde[i]) &&
              kolumn_info$max_varde[i] > kolumn_info$min_varde[i]) {
            c(kolumn_info$min_varde[i], kolumn_info$max_varde[i])
          } else if (isTRUE(kolumn_info$ar_numerisk[i])) {
            # Numerisk kolumn men min==max (eller data saknas) – riktig
            # slider vore missvisande/låst ändå, ge den samma dummypar
            # som textkolumnerna så fältet åtminstone går att skriva i.
            c("a", "b")
          } else {
            c("a", "b")
          }
        }),
        kolumn_info$name
      ),
      stringsAsFactors = FALSE
    )

    DT::datatable(
      platshallare,
      rownames = FALSE,
      filter = "top",
      escape = TRUE,
      callback = DT::JS(
        "
    table.on('draw.dt', function() {
      table.cells().every(function() {
        var cell = this.node();
        var text = $(cell).text();
        $(cell).attr('title', text);
      });

      $(table.table().header()).find('th').each(function() {
        var text = $(this).text();
        $(this).attr('title', text);
      });

      // scrollX + scrollY klonar tabellhuvudet till en separat <table>
      // med egen breddberäkning. Görs inte om efter varje ritning kan
      // huvud och kropp hamna i otakt.
      setTimeout(function() { table.columns.adjust(); }, 0);

      // Speglar aktiva kolumnfilter till en Shiny-input, eftersom vår
      // egen ajax-källa (till skillnad från DT:s inbyggda server=TRUE-
      // läge) inte gör detta automatiskt. Nedladdningsknapparna läser
      // input$preview_search_columns för att bygga samma SQL-villkor.
      var sokvarden = table.columns().search().toArray();
      Shiny.setInputValue('preview_search_columns', sokvarden, {priority: 'event'});
    });

    table.on('init.dt', function() {
      table.columns.adjust();

      var ns = '.dtColAdjust_' + table.table().node().id;
      $(window).off(ns).on('resize' + ns, function() {
        table.columns.adjust();
      });
    });

    // Byte av län/kommun i shinyWidgets-pickern är INTE en DT-intern
    // trigger (sidbyte/sortering/kolumnfilter) – DT vet inte att den ska
    // ladda om data bara för att en helt annan Shiny-input ändras. R-sidan
    // skickar därför ett meddelande hit varje gång geo_vald() ändras, se
    // observeEvent(geo_vald(), ...). false = behåll aktuell sida/sortering,
    // ladda bara om med samma parametrar (nu med nytt WHERE-villkor).
    Shiny.addCustomMessageHandler('dt_reload_preview', function(msg) {
      table.ajax.reload(null, false);
    });
    "
      ),
      options = list(
        serverSide = TRUE,
        # type = "POST" måste matcha hur filter_fn läser parametrarna
        # (req$rook.input$read(), dvs. kroppen) – annars skickar klienten
        # GET och kroppen är tom.
        ajax = list(url = ajax_url, type = "POST"),
        searchDelay = 600,
        scrollX = TRUE,
        scrollY = "calc(100vh - 230px)",
        scrollCollapse = TRUE,
        pageLength = 25,
        autoWidth = TRUE,
        dom = "tip",
        columnDefs = list(
          list(
            targets = "_all",
            className = "dt-nowrap"
          )
        )
      )
    )
  }, server = FALSE)

  # geo_vald() (län/kommun-pickern) ändras utan att aktuell_kalla()/
  # output$preview reaktivt beror på den (medvetet – annars skulle hela
  # DT-widgeten byggas om istället för att bara hämta nya rader). Instruera
  # i stället klientens redan uppkopplade tabell att ladda om via ajax.
  observeEvent(geo_vald(), {
    session$sendCustomMessage("dt_reload_preview", list())
  }, ignoreInit = TRUE)

  output$export_info_text <- renderText({
    kalla <- aktuell_kalla()
    req(kalla$sql_bas)

    kolumn_info <- kolumninfo_cache(
      kalla$kolumn_info_key, kalla$con_fun, kalla$sql_bas
    )

    # OBS: bygger geo_where_fn direkt här (inte kalla$geo_where_fn, som är
    # isolate()-skyddad för AJAX-bruk – se aktuell_kalla()). Den här
    # renderText körs i en riktig reaktiv kontext, så geo_vald() ska
    # anropas direkt för att texten ska uppdateras när området byts.
    geo <- geo_vald()
    geo_where_fn <- function(con) {
      if (identical(input$visa, "ftg")) ftg_where_sql(con, geo) else arb_where_sql(con, geo)
    }

    antal <- tryCatch(
      hamta_antal_sql(
        kalla$con_fun, kalla$sql_bas, geo_where_fn,
        input$preview_search_columns, kolumn_info
      ),
      error = function(e) {
        warning(conditionMessage(e))
        NULL
      }
    )

    req(antal)

    filter_pa <- kolumnfilter_aktivt(input$preview_search_columns)

    paste0(
      "Rader i urvalet: ",
      format(antal$filtrerat, big.mark = " ", scientific = FALSE),
      if (filter_pa) {
        paste0(
          " av ", format(antal$totalt, big.mark = " ", scientific = FALSE)
        )
      } else {
        ""
      },
      if (antal$filtrerat > excel_max_rader) " – laddas ned som CSV i ZIP." else ""
    )
  })

  # ── Direktlänkar till statiska zip-filer ──────────────────────────────────
  # Filerna byggs av ett fristående cron-skript (cron_bygg_nedladdningszip.R),
  # inte av appen. reactiveFileReader pollar filens ändringstid var 30:e
  # sekund, så länken (och filstorleken) uppdateras automatiskt om cron
  # bygger om zippen medan en session redan är öppen – utan att appen
  # behöver veta något om NÄR eller VARFÖR filen ändrades.

  direktlank_ui <- function(namn) {
    fil <- zip_fil(namn)

    if (!file.exists(fil)) {
      return(NULL)
    }

    tags$a(
      class = "rd-direktlank",
      href = paste0("nedladdning/", basename(fil)),
      download = NA,
      title = paste0(
        "Hela datasetet, zippad CSV. Byggs av ett nattligt jobb – kan ",
        "vara någon dag äldre än databasen, oavsett valt område ovan."
      ),
      paste0("Hela datasetet, zippad CSV (", filstorlek_text(fil), ")")
    )
  }

  zip_lasare <- function(namn) {
    shiny::reactiveFileReader(
      intervalMillis = 30000,
      session = session,
      filePath = zip_fil(namn),
      readFunc = function(fil) if (file.exists(fil)) file.mtime(fil) else NULL
    )
  }

  zip_mtime_ftg <- zip_lasare("foretag")
  zip_mtime_arb <- zip_lasare("arbetsstallen")

  output$direktlank_ftg <- renderUI({
    zip_mtime_ftg()
    direktlank_ui("foretag")
  })

  output$direktlank_arb <- renderUI({
    zip_mtime_arb()
    direktlank_ui("arbetsstallen")
  })

  # ── Nedladdning – Företag ─────────────────────────────────────────────────

  output$ladda_ned_ftg <- downloadHandler(
    filename = function() {
      geo_str <- filnamn_sakert(geo_text(geo_vald(), geo_lookup()))
      kolumn_info <- kolumninfo_cache("kolumner_foretag", ftg_con_fun, ftg_sql_bas)

      antal <- hamta_antal_sql(
        ftg_con_fun, ftg_sql_bas,
        function(con) ftg_where_sql(con, geo_vald()),
        input$preview_search_columns, kolumn_info
      )

      filandelse <- if (antal$filtrerat <= excel_max_rader) "xlsx" else "zip"

      paste0("foretag_", geo_str, "_", Sys.Date(), ".", filandelse)
    },
    content = function(file) {
      geo_str <- filnamn_sakert(geo_text(geo_vald(), geo_lookup()))
      kolumn_info <- kolumninfo_cache("kolumner_foretag", ftg_con_fun, ftg_sql_bas)

      df <- hamta_filtrerat_export(
        ftg_con_fun, ftg_sql_bas,
        function(con) ftg_where_sql(con, geo_vald()),
        input$preview_search_columns, kolumn_info
      )

      skriv_tabell_excel_eller_zip(
        df = df,
        file = file,
        basnamn = paste0("foretag_", geo_str, "_", Sys.Date())
      )
    }
  )

  # ── Nedladdning – Arbetsställen, tabell ───────────────────────────────────

  output$ladda_ned_arb <- downloadHandler(
    filename = function() {
      geo_str <- filnamn_sakert(geo_text(geo_vald(), geo_lookup()))
      sql_bas <- arb_sql_bas()
      kolumn_info <- kolumninfo_cache("kolumner_arbetsstallen", arb_con_fun, sql_bas)

      antal <- hamta_antal_sql(
        arb_con_fun, sql_bas,
        function(con) arb_where_sql(con, geo_vald()),
        input$preview_search_columns, kolumn_info
      )

      filandelse <- if (antal$filtrerat <= excel_max_rader) "xlsx" else "zip"

      paste0("arbetsstallen_", geo_str, "_", Sys.Date(), ".", filandelse)
    },
    content = function(file) {
      geo_str <- filnamn_sakert(geo_text(geo_vald(), geo_lookup()))
      sql_bas <- arb_sql_bas()
      kolumn_info <- kolumninfo_cache("kolumner_arbetsstallen", arb_con_fun, sql_bas)

      df <- hamta_filtrerat_export(
        arb_con_fun, sql_bas,
        function(con) arb_where_sql(con, geo_vald()),
        input$preview_search_columns, kolumn_info
      )

      skriv_tabell_excel_eller_zip(
        df = df,
        file = file,
        basnamn = paste0("arbetsstallen_", geo_str, "_", Sys.Date())
      )
    }
  )

  # ── Nedladdning – Arbetsställen, geopackage ───────────────────────────────

  output$ladda_ned_arb_gpkg <- downloadHandler(
    filename = function() {
      geo_str <- filnamn_sakert(geo_text(geo_vald(), geo_lookup()))
      paste0("arbetsstallen_", geo_str, "_", Sys.Date(), ".gpkg")
    },
    content = function(file) {
      sql_bas <- arb_sql_bas()
      kolumn_info <- kolumninfo_cache("kolumner_arbetsstallen", arb_con_fun, sql_bas)

      df <- hamta_filtrerat_export(
        arb_con_fun, sql_bas,
        function(con) arb_where_sql(con, geo_vald()),
        input$preview_search_columns, kolumn_info
      )

      sf::st_write(
        arb_till_sf(df),
        file,
        driver = "GPKG",
        quiet = TRUE
      )
    }
  )
}

shinyApp(ui, server)
