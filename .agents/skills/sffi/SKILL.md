---
name: sffi
description: Select and implement Simple FFI boundaries while preferring in-tree pure-Simple counterparts, especially PureDatabase over C SQLite wrappers.
---

# SFFI selection

Read `doc/00_llm_process/llm_wiki.md`, then search the repository for a
pure-Simple counterpart before adding foreign bindings. “Simple embedded DB”
means `std.database.pure_sql.PureDatabase`; `sqlite_sffi` means C SQLite.
PostgreSQL-mimic server work composes `std.database.postgres_mimic` with
`PureDatabase`. Production database execution uses cached SMF/LSM or native
artifacts even when initiated by an interpreter-mode caller.
