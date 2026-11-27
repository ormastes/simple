---
name: sffi
description: Use or review Simple FFI boundaries, distinguish native Simple counterparts from foreign wrappers, and select pure-Simple database engines before SQLite/PostgreSQL SFFI. Trigger for SFFI, FFI wrappers, native libraries, or database backend selection.
---

# SFFI

Before adding an `extern fn` or foreign-library wrapper:

1. Read `doc/00_llm_process/llm_wiki.md` for repository aliases.
2. Search `src/lib/**` and `src/os/**` for a pure-Simple counterpart using the
   capability name and synonyms.
3. Use SFFI only when the requested capability genuinely requires foreign code.
4. Keep extern ownership in the canonical no-GC sync backend; compatibility
   families should export that owner rather than duplicate runtime hooks.
5. Verify wrapper ABI, error propagation, ownership, and compiled execution.
6. Run `scripts/audit/sffi-unsafe-backlog.shs` when reviewing direct `rt_*`
   use. Its result is a source-only warning queue, never signed/provider
   admission evidence. Do not blanket-autofix calls: use an approved
   per-contract safe facade mapping, or add only the exact declaration tag and
   smallest lexical `unsafe(capabilities: [ffi])` scope while preserving ABI,
   error/null semantics, ownership, call count, and hot-path allocation/copy
   behavior. Otherwise leave the boundary explicitly unsafe and track it.

Database rule:

- “Simple embedded DB” / “Simple SQLite” means
  `std.database.pure_sql.PureDatabase` unless C SQLite is explicitly requested.
- `sqlite_sffi` is the C SQLite adapter, not the pure-Simple engine.
- PostgreSQL-compatible Simple server work belongs under
  `std.database.postgres_mimic` and composes `PureDatabase`.
- Production database paths use cached SMF/LSM or native executable artifacts,
  including when the caller itself runs in interpreter mode.

Detailed SFFI reference: `doc/07_guide/platform/ffi/sffi.md`.

## rt_ mapping and pointer checks

After changing an `rt_` extern, its C provider, or a Rust twin, run:

- `python3 scripts/check/check-rt-pointer-ref-map.py`: pointer returns and parameters
- `python3 scripts/check/check-rt-host-map.py`: per-host mapping
- `python3 scripts/check/check-rt-c-contract-compile.py`: compiles Simple signatures against C (on demand)

A C return that can be NULL must be `T?` in Simple. If the function has no error channel, fail closed in C with `SIMPLE_RT_NONNULL` (`src/runtime/runtime_nonnull.h`). Never change a return type on lint status alone. Change a width everywhere: `runtime.h`, every C provider and preprocessor branch, selfchecks, `runtime_sffi.rs` spec and tests, Rust twins, and LLVM declarations. UNKNOWN and UNTESTED are never PASS. Baselines only shrink. See `doc/05_design/compiler/rt_mapping_pointer_contract_design.md`.
