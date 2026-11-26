# Three TOCTOU sibling specs were left uncompilable by the 2026-10-01 release/1.0 transplant

- **Date:** 2026-11-26
- **Status:** OPEN
- **Introduced by:** `88aac2ffe28` "rebase(main): transplant current main tree onto release/1.0"
  (2026-10-01). It is the last commit to touch each of the three files.
- **Blocks:** final verification of `gpu_probe_then_create_toctou_2026-08-04`.

## Defect

The transplant merged main's and release's versions of each file and dropped definitions that the
surviving bodies still call. Each spec now fails with a semantic error instead of exercising the
probe-then-create path. Results on Linux aarch64 GB10, seed sha256 prefix `fb80903917d6d5f5`:

| spec | result | first error |
|---|---|---|
| `test/01_unit/lib/gc_async_mut/ui/web_render_pixel_backend_queue_spec.spl` | 3/5 | `:211:9: variable 'probe' not found`. The `val probe = Engine2D.probe_backend(64, 48, "vulkan")` line and the `Engine2D` / `BackendStatus` imports were dropped. |
| `test/05_perf/graphics_2d/backend_probe_spec.spl` | 0/3 | `:88:13: function 'make_ok_sentinel' not found` |
| `test/03_system/gui/draw_backend_matrix/proc_draw_combo_spec.spl` | 8/12 | `function 'assert_metal_processing_half' not found` (defined at line 137 of `d921e11599e`, the transplant's parent) |

## Why a plain restore is wrong

Checking all three files out from `d921e11599e` makes `backend_probe_spec` 6/6 and
`proc_draw_combo_spec` 12/12, and both stay honest under `SIMPLE_2D_CREATE_FAULT=vulkan`.
`web_render_pixel_backend_queue_spec` goes to 4/5; its one red is the pre-existing Draw IR
material-fallback example. But the restore also deletes the ten main-side
`AC-1: probe result carries ...` examples in `backend_probe_spec`. The repair is a three-way
merge: restore the missing helpers and imports into the current files and keep both sides'
examples.
