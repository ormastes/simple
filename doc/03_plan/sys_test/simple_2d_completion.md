# System Test Plan: Simple 2D Completion

- **Date:** 2026-11-28
- **Status:** Active (`release/1.0.0`)
- **Requirements:** `doc/02_requirements/feature/simple_2d_completion.md` (`REQ-S2D-001..007`)
- **NFRs:** `doc/02_requirements/nfr/simple_2d_completion.md` (`NFR-S2D-001..006`)

---

## 1. Test Coverage Matrix

| Requirement / NFR | Spec File | Expected Outcome | Manual Path (`doc/06_spec/`) |
|---|---|---|---|
| `REQ-S2D-001`, `NFR-S2D-001` | `test/02_integration/rendering/engine2d_focused_window_corner_device_spec.spl` | Remove `@tag:in-development`; `0` diff pixels at focused window corners between CPU & Vulkan. | `doc/06_spec/02_integration/rendering/engine2d_focused_window_corner_device_spec.md` |
| `REQ-S2D-002`, `REQ-S2D-003`, `NFR-S2D-003` | `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_damage_plan_rejection_spec.spl`, `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl`, `test/02_integration/rendering/engine2d_retained_group_opacity_damage_spec.spl` | Prepared damage plan & single-root damaged executor admit `opacity_milli < 1000` with `surface_id != ""` while rejecting anonymous/invalid/parent-sampling batches; Vulkan offscreen pooling & device composite execute with `0` readback in steady state. | `doc/06_spec/02_integration/rendering/engine2d_retained_group_opacity_damage_spec.md` |
| `REQ-S2D-004`, `NFR-S2D-001` | `test/02_integration/rendering/engine2d_wm_local_lane_clock_tick_spec.spl` | Clock tick on `default`, `fluid_light`, and `aetheric_dark` takes retained damage path and matches fresh frame. | `doc/06_spec/02_integration/rendering/engine2d_wm_local_lane_clock_tick_spec.md` |
| `REQ-S2D-001`, `NFR-S2D-001` | `test/02_integration/rendering/engine2d_themed_wm_fresh_device_spec.spl`, `test/02_integration/rendering/engine2d_embedded_surface_spec.spl` | All existing themed WM & embedded surface tests remain green (`0` regressions). | `doc/06_spec/02_integration/rendering/engine2d_embedded_surface_spec.md` |
| `REQ-S2D-005`, `REQ-S2D-006`, `NFR-S2D-002` | `test/03_system/gui/reftest/parity/reftest_spec.spl` | All `11/11` scenes (`porter_duff`, `mix_blend_mode`, `backdrop_filter`, `opacity_layer`, etc.) pass within `+-2` LSB. | `doc/06_spec/03_system/gui/reftest/parity/reftest_spec.md` |
| `REQ-S2D-005..007`, `NFR-S2D-002`, `NFR-S2D-006` | `test/01_unit/lib/skia/cpu_backend_blend_layer_matrix_spec.spl` | Verifies shear/skew matrix round-trip through `SkCanvas`, `DrawImage` blend modes (`Multiply`/`DstIn`), `DrawPath`/`DrawRRect`/`DrawPaint` non-`SrcOver` modes, coverage-weighted AA blending, and nested `SaveLayer` isolation. | `doc/06_spec/01_unit/lib/skia/cpu_backend_blend_layer_matrix_spec.md` |

## 2. Execution Discipline

- While the 1-core `P4:cli-release` build runs on the host, execute **one single-file** `<simple_bin> test --no-session-daemon <spec>` at a time.
- Check `find doc/06_spec -name '*_spec.spl' | wc -l` prints `0` before every commit.
- Run `sh scripts/audit/direct-env-runtime-guard.shs --working` and `--staged` before opening each PR.
