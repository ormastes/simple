# Seed and stage2 resolve `std.fs` to different files (`fs/__init__.spl` vs `fs.spl`)

Status: open. Record only, no fix. Mitigated for `std.fs` by `50abed005d5`
(both files re-export one body from `nogc_sync_mut/fs/text_io.spl`).

## Divergence

`src/lib/nogc_async_mut/` and `src/lib/nogc_sync_mut/` each contain BOTH
`fs.spl` and `fs/__init__.spl`. The two resolvers disagree on which one
`use std.fs` names:

| Resolver | Code | Winner for `std.fs` |
|---|---|---|
| Rust seed interpreter | `src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs`, `try_variant_stdlib_root` (line 499: "Package (__init__.spl) wins over a same-named file HERE, deliberately") | `nogc_async_mut/fs/__init__.spl` (the package) |
| Rust seed, generic stdlib subdir loop | same file, line 894 ("File wins over a same-named package directory") | file, but only reached when the variant fast path misses |
| Pure-Simple (stage2) | `src/compiler/80.driver/driver_source_loading.spl` `_driver_resolve_entry_import_exact` family loop (`.spl`, then `/mod.spl`, then `/__init__.spl`) | `nogc_async_mut/fs.spl` (the file) |

So the seed has two opposite precedence rules, and stage2 matches only the
fallback one.

## Evidence (2026-10-09/10)

- `_driver_resolve_entry_import("std.fs", "src/app/log")` returns
  `src/lib/nogc_async_mut/fs.spl` (spec
  `test/01_unit/compiler/80.driver/std_fs_file_vs_package_resolution_spec.spl`).
- Before `25fbd168fa3`, `file_read_text` / `file_write_text` /
  `dir_children` were defined only in `fs/__init__.spl`. The seed ran
  `use std.fs.{file_read_text, dir_children}` fine (probe spec printed
  `a=12890 ... kids=22`). Stage2 failed to resolve the same import, because
  `fs.spl` did not export those names.
- After deleting the package copies, the seed failed with `semantic: function
  dir_children not found`, even though `fs.spl` exported it. That confirms
  the seed resolves to the PACKAGE. Re-exporting from inside the package via
  `use std.nogc_sync_mut.fs.{...}` also failed: the seed's fast path resolves
  that spelling back to the package itself.
- Importers depend on both shapes: some import file-only names (`File`,
  `read_to_string`, `rt_file_read_text`), others package-only names
  (`file_read_text`, `dir_children`). See `git grep "use std.fs.{"`.

## Documented rule

- `doc/07_guide/language/module_system.md:107`: "`mod router` resolves to
  either `router.spl` or `router/__init__.spl`. If both exist, the compiler
  reports an error."
- `src/compiler_rust/compiler/src/module_resolver/mod.rs:11`: "Module
  resolution is unambiguous (no foo.spl + foo/__init__.spl conflicts)".

Neither resolver enforces this. Both pick a winner silently, and they pick
different winners.

## Open decisions

1. Make the seed fast path and stage2 agree. Either file-first everywhere
   (the seed's own subdir-loop comment says package-first broke
   `use std.spec`), or package-first everywhere.
2. Or enforce the documented error and fold each `x.spl` + `x/__init__.spl`
   pair into one. A census of other same-named pairs under `src/lib` is
   needed first (`fs`, `io`, `spec` are known).
