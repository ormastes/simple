---
id: test_helpers_namespace_unresolved_deep_paths_2026-07-06
status: OPEN
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
