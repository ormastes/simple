---
id: test_helpers_namespace_unresolved_deep_paths_2026-07-06
status: RESOLVED
severity: medium
discovered: 2026-07-06
discovered_by: backend-only direct spec authoring (test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_only_direct_spec.spl)
related: test/helpers/gpu_draw_event_shared.spl
related: src/app/test_runner_new/
---

# `test.helpers.*` module namespace fails to resolve from deep (depth ≥ 5) spec paths

## Summary

`use test.helpers.gpu_draw_event_shared.{...}` resolves from shallow spec
directories but fails with `error: semantic: Cannot resolve module:
test.helpers.gpu_draw_event_shared` once the importing spec sits five or more
directory levels below `test/`.

## Reproduction (bisected 2026-07-06)

Identical one-line-import probe spec placed at increasing depths under
`test/01_unit/`:

| Spec path | Depth below `test/` | `test.helpers` resolves? |
|-----------|---------------------|--------------------------|
| `test/01_unit/_probe_spec.spl` | 1 | YES |
| `test/01_unit/lib/_probe_spec.spl` | 2 | YES |
| `test/01_unit/lib/gc_async_mut/_probe_spec.spl` | 3 | YES |
| `test/01_unit/lib/gc_async_mut/gpu/_probe_spec.spl` | 4 | YES |
| `test/01_unit/lib/gc_async_mut/gpu/engine2d/_probe_spec.spl` | 5 | **NO** |

The existing helper consumers all live at depth 3 (e.g.
`test/02_integration/lib/gpu/…`, `test/03_system/gui/draw_backend_matrix/…`),
which is why this was never hit before.

## Impact

Specs under the deep `test/01_unit/lib/<family>/<domain>/<topic>/` layout
(which mirrors the `src/lib/` tree, so depth ≥ 5 is normal) cannot reuse the
shared `test/helpers/*` modules. In `backend_only_direct_spec.spl` this forced
inlining the two tiny leaf helpers (`assert_color_eq`, `read_pixels_ppm`)
instead of importing them from `test/helpers/gpu_draw_event_shared.spl` — a
duplication the project's DRY rule normally forbids.

## Root Cause (hypothesis)

The `test.` namespace root is located by walking parent directories up from the
importing spec, and the walk is capped at ~4 ancestor levels. Beyond that the
`test/` root is never found and the module cannot be resolved. Fix is likely to
anchor the `test.` namespace at the repo/test root unconditionally (as `std.`
is anchored at `src/lib/`) rather than by bounded parent-walk.

## Workaround in place

`backend_only_direct_spec.spl` imports `encode_ppm_p6` from
`std.common.image.ppm_decode` and the `color_*` channel accessors from
`std.gc_async_mut.gpu.engine2d.color`, and defines local 4-line
`assert_color_eq` / `read_pixels_ppm` mirrors of the shared helper, with a
comment pointing back here. Remove the local mirrors and restore the
`test.helpers` import once this resolves.

## 2026-11-25 verification (release/1.0.0, worktree p2w6-ab) — RESOLVED

STALE — the root cause was fixed by commit `22ae61c672e` "fix(resolve):
test.* imports from specs under lib family dirs" (2026-11-05, ancestor of
release/1.0.0 HEAD `64dfa6d980f`). The ancestor climb in
`src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs:814-829`
no longer stops at a nested directory that merely contains a `src/` folder;
it climbs to the workspace boundary, so `test.*` imports from specs at any
depth reach `<repo>/test`. Regression spec:
`test/01_unit/lib/nogc_sync_mut/resolve/test_import_under_src_dir_spec.spl`.

Executable evidence on this host (deployed `bin/simple.exe`, Rust seed
v1.0.0-rc.1): a one-line probe placed at the exact failing depth from the
original bisect (`test/01_unit/lib/gc_async_mut/gpu/engine2d/`, depth 5)
with `use test.helpers.gpu_draw_event_shared.{read_pixels_ppm}` and a real
call ran to completion — `PROBE_OK len=14`, exit 0. The probe file was
removed after the run.

Follow-up left open deliberately: the workaround mirrors in
`test/01_unit/lib/gc_async_mut/gpu/engine2d/backend_only_direct_spec.spl`
(local `assert_color_eq` / `read_pixels_ppm`, lines ~60-64) can now be
replaced by the `test.helpers` import per the workaround note above, but
that edit cannot be verified on this host because `bin/simple.exe test`
fails repo-wide at this HEAD (`unknown decorator '@representation_boundary'`
in `src/app/test_runner_new/test_runner_client.spl:9:1`, pinned-seed/source
mismatch). The doc is closed; the cleanup is a mechanical follow-up for a
lane with a working spec runner.
