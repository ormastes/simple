# std.io facade bare-exports `dir_exists`/`file_exists` it never backs (Stage 2 `compiler_cli_build` HIR fatal)

- **ID:** std_io_facade_bare_export_dir_exists_unbacked_2026-11-06
- **Severity:** P1 (blocks Stage 2 bootstrap row `compiler_cli_build`)
- **Status:** fix-implemented-verification-pending (full row not re-run)
- **Scope:** stdlib facade source (`src/lib/nogc_async_mut/io.spl`), plus a
  separate source defect in `src/compiler/00.common/dependency/resolution.spl:106`
- **Found:** bootstrap run 12, tree `fadd88059b3`, Stage 2 sha256 `e48b6137cb84ee8e…`

## Symptom

```
[hir-reexport-chase-unresolved] facade=lib.nogc_async_mut.io item=dir_exists local=dir_exists importer=src/compiler/00.common/dependency/resolution.spl ...
HIR lowering error in src/compiler/00.common/dependency/resolution.spl: unresolved name: dir_exists at :117:31
```

`resolution.spl:16` is `use std.io.{file_exists, dir_exists}`.

## Root cause

`std.io` resolves to the FILE-form facade `src/lib/nogc_async_mut/io.spl`
(the diag run shows `mname=lib.nogc_async_mut.io imports=19`, matching that
file; `io/__init__.spl` is never loaded). Lines 139-141 listed
`file_exists`/`dir_exists` in a bare `export a, b, ...` block, but the file
neither declares nor imports either name. A bare export of an undeclared,
unimported name can only be answered by package-sibling inference
(`module_reexport_materialization.spl` "BARE `export Name`" arm) or the
closure-wide unique-owner fallback (`try_register_bootstrap_global_symbol`,
`module_import_registration.spl:1100`). Both depend on which modules the
build closure happens to contain:

| closure | file_exists | dir_exists |
|---|---|---|
| single-entry resolution.spl (91 modules) | chase miss, rescued by unique owner | chase miss, rescued by unique owner |
| full row run 12 (3056 modules) | found via a `lib.nogc_async_mut` sibling that imports it (e.g. `db_atomic.spl`) | chase miss, **2+ owners** (`nogc_sync_mut/io_runtime.spl:661`, private `nogc_sync_mut/env/paths.spl:239`) -> fatal |

Diag (`SIMPLE_BOOTSTRAP_DIAG=1 SIMPLE_HIR_SIBPROBE=1`): `[sibprobe] facade=lib.io
module_name=lib.nogc_async_mut.io package=lib.nogc_async_mut siblings=1` ->
`[sibprobe-miss] ... matches=0 complete=true valid=true`. That is a correct,
complete negative, not a chase/memo defect. No module in the tree routes
`dir_exists` through `std.nogc_sync_mut.io` either: the sync facade
(`io.spl`, `io/__init__.spl`, `dir_ops.spl`) never exports it, so the
`io/__init__.spl` route `export use std.nogc_sync_mut.io.{..., dir_exists, ...}`
was dead too. Precedent for treating this as a facade-source defect:
`322b031da1d` fixed the same class in the same file for the time/debug helpers
("a bare `export` binds nothing").

### Why run 11's full row did not hit it

`resolution.spl` was not in the run-11 closure (zero mentions in its 19 MB
row log; HIR total 3049). `7a77c04f049` (in `e4c8830efc7..fadd88059b3`) added
`use compiler.common.dependency.{member_access_scope_for_modules, ...}` to
`src/compiler/20.hir/hir_lowering/_Items/module_import_registration.spl`; the
package `__init__` does `export resolution.*`, which pulled `resolution.spl`
into the closure (3049 -> 3056 modules).

## Fix

- `src/lib/nogc_async_mut/io.spl`: drop `file_exists`/`dir_exists` from the
  bare block; `export use std.nogc_sync_mut.io.{file_exists}` and
  `export use std.nogc_sync_mut.io_runtime.{dir_exists}`.
- `src/lib/nogc_async_mut/io/__init__.spl`: same dead `dir_exists` route
  replaced by `export use std.nogc_sync_mut.io_runtime.{dir_exists}`.
- `src/compiler/00.common/dependency/resolution.spl:106`: `segs[i].name()` ->
  `segs[i].name`. `Segment` has a `name` FIELD and no `name` method; the seed
  rejects the same shape (`Runtime error: Function 'Seg.name' not found`). This
  is the separate MIR fatal `unresolved method call: name ... Segment::name`,
  not a consequence of the HIR miss.

No compiler change: the compiler's negative answer is correct.

## Still open (not fixed here)

- The rest of the `io.spl` host-helper bare-export block (`shell`, `file_read`,
  `env_get`, `process_run`, ...) has the same unbacked shape and resolves only
  through closure-dependent sibling/unique-owner rescue.
- The `via_sibling` arm counts a sibling that merely IMPORTS a name as an
  owner route, which is what made `file_exists` resolve in the full row.
- `resolution.spl:107-109` `build_module_path` has a dangling `path`
  expression before `path + "/__init__.spl"`, so `to_file_path` yields
  `.../__init__.spl.spl`.

## Evidence

See the commit message for Stage 2 hashes and run results. Spec:
`test/01_unit/compiler/hir/async_io_facade_host_helper_reexport_spec.spl`.

## Landing note (2026-11-06)

While this branch was in review, `90f91052fae` ("route async facade host helpers from their
concrete owners") landed the same facade repair more completely: every bare helper export in
`io.spl` now goes through `export use std.nogc_sync_mut.io.{...}`, and `dir_exists` through
`io_runtime`. On rebase both facade files were taken from origin. This branch now carries only
the `resolution.spl` field read (`segs[i].name`), the spec (which pins no bare
`file_exists`/`dir_exists` export, the `io_runtime` route in both facades, and the field read),
and this record.
