# Unexported name imported via `std.io_runtime` facade -> HIR unresolved name (2026-11-22)

Status: FIXED (#10770 `db23cc27214`), guarded (#10777 `ecff7320c13`).

## Symptom
Phase 3, integ25 Stage 2 native-building Stage 3 from release `3866b2a4b8c` (go-to-end):

```
[go-to-end] failed stage=hir module=compiler.backend.runtime_c_compile_pool_v1:
HIR lowering error in .../runtime_c_compile_pool_v1.spl: unresolved name: cpu_count_checked
```

## Root cause
`runtime_c_compile_pool_v1.spl:12` (added by `e0aea49c8e9`) imported
`use std.io_runtime.{process_spawn_async, cpu_count_checked}`. Tier-less
`std.io_runtime` resolves to the root facade `src/lib/io_runtime.spl` (direct
`lib/` path is tried before the tier search,
`src/compiler/99.loader/module_resolver/resolution.spl`). The facade's explicit
`export ... from` list has no `cpu_count_checked`, and none of the four tier
`io_runtime` variants export it either, so no tier ordering could resolve it.
The same gap existed for `dir_list` (11 example/app files) and `file_read_text`
(2 test_runner probes).

## Fix
Import-only: `cpu_count_checked` from `std.nogc_sync_mut.io.sysinfo_ops`,
`dir_list` from `std.nogc_sync_mut.io.dir_ops`, `file_read_text` from
`std.nogc_sync_mut.io.file_ops`. No logic change.

## Evidence
- integ25 Stage 2 compiler, `compile --format=smf` (8G-capped scope): the red
  fixture `test/fixtures/io_runtime/red_unexported_name.spl` emits
  `[hir-reexport-chase-unresolved] facade=lib.io_runtime item=cpu_count_checked`;
  the green fixture `green_exported_name.spl` emits none. (SMF mode only warns;
  the hard error is at native-build.)
- Guard replay on the pre-#10770 blobs FAILs naming `cpu_count_checked`,
  `file_read_text`, `dir_list`; current tree PASSes (2630 names, 1114 files).
- Not yet observed: a full integ25 Phase 3 rerun past this module.

## Guard
`sh scripts/check/check-io-runtime-facade-imports.shs` — bootstrap-tier advisory
row in `config/check/must_check_gates.sdn` (like `tierless-std-js-imports`), not
in the push tier. Known gaps: does not scan `test/`; selftest covers only the
single-line brace form.
