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

## rt_ mapping and pointer checks

After changing an `rt_` extern, its C provider, or a Rust twin, run:

- `python3 scripts/check/check-rt-pointer-ref-map.py`: pointer returns and parameters
- `python3 scripts/check/check-rt-host-map.py`: per-host mapping
- `python3 scripts/check/check-rt-c-contract-compile.py`: compiles Simple signatures against C (on demand)

A C return that can be NULL must be `T?` in Simple. If the function has no error channel, fail closed in C with `SIMPLE_RT_NONNULL` (`src/runtime/runtime_nonnull.h`). Never change a return type on lint status alone. Change a width everywhere: `runtime.h`, every C provider and preprocessor branch, selfchecks, `runtime_sffi.rs` spec and tests, Rust twins, and LLVM declarations. UNKNOWN and UNTESTED are never PASS. Baselines only shrink. See `doc/05_design/compiler/rt_mapping_pointer_contract_design.md`.
