# Web Stack Sample Architecture

## Purpose

`examples/web_stack_sample/` is the canonical verification target for the
Simple web stack. It is intentionally smaller than `examples/webapp/` while
still exercising auth/session, CRUD, and search/filter in one app.

## Storage Split

- `std.web_framework.persistence.WebRecordStore<T>` is the backend-neutral
  record abstraction used by the sample model layer.
- `sqlite` mode delegates CRUD to `std.database.sql.repository.Repository<T>`.
- `simpledb` mode persists rows into `std.database.SdnDatabase` tables using
  `SimpleDbRecordAdapter<T>`.

## Session Path

- `std.web_framework.session.SessionStore` now supports two constructors:
  `SessionStore.sqlite(db)` and `SessionStore.simpledb(db)`.
- The same selected backend stores both application records and sessions, so
  auth/session behavior is exercised in both lanes.

## App Selection

- `std.web_framework.app.AppConfig` now includes:
  - `backend_kind`
  - `db_path`
  - `simpledb_path`
- `WebApp.from_config` opens the selected backend and initializes the matching
  session store.

## Verification Surface

- Source contract tests verify:
  - backend selection wiring
  - required routes
  - stable browser markers and form actions
  - backend-neutral persistence/session abstractions
