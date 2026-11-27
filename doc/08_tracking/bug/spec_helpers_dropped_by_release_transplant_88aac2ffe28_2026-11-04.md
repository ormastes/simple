# Spec helper definitions dropped by release transplant 88aac2ffe28

- Status: fixed for the two named specs (2026-11-04, see wm_metal_glass_multi_receipt_opacity_2026-07-27.md); window_scene_draw_ir 12/12, host_compositor_entry 55/63 (remaining reds recorded there)
- Found: 2026-11-04 (lane 4, macOS native run of Metal glass acceptance specs)
- Platform: shared (not macOS-specific)

`88aac2ffe28` ("rebase(main): transplant current main tree onto release/1.0")
rewrote two acceptance specs and dropped their top-level helper definitions
while keeping the call sites:

| file | defs at 88aac2ffe28~1 | defs at origin/release/1.0.0 / origin/main |
|---|---|---|
| test/01_unit/os/compositor/host_compositor_entry_spec.spl | `_metal_material_composition`, `HOST_COMPOSITOR_CORE_SRC`, … | 0 (10 call sites on main) |
| test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl | `_translucent_fallback_snapshot`, … | 0 (2 call sites on main) |

Result on release/1.0.0 (seed, interpreter): host_compositor_entry 42/61,
window_scene_draw_ir 4/12, failing with `function ... not found` /
`variable HOST_COMPOSITOR_CORE_SRC not found`.

Restoring the pre-transplant files is NOT a sufficient fix: they then run
53/63 and 7/12, with other reds (source/spec drift and seed-interpreter
semantic errors such as `cannot assign to const 'comp'`). Needs an owner
who reconciles each spec against current source. Check the stale-snapshot
rewind recipe (doc/07_guide/infra/vcs/stale_merge_snapshot_rewind.md) for
other files in the same transplant.
