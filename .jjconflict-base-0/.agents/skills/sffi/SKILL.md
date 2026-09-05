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

For a direct `rt_*` review, run `scripts/audit/sffi-unsafe-backlog.shs`. Its
output is a source-only warning queue, not verified/signed provider evidence.
Never blanket-autofix the calls: use an approved per-contract safe-facade
mapping, or add only the exact raw declaration annotation and smallest lexical
`unsafe(capabilities: [ffi])` scope while preserving ABI, error/null semantics,
ownership, call count, and hot-path allocation/copy behavior. Otherwise retain
the explicit unsafe boundary and track the migration.
