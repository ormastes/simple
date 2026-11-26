# WM content damage-plan API: specified by two specs, never landed

Status: open. Measured 2026-11-26 on release/1.0.0 `f2f5776b73f`, seed
`cargo-target-wr-seed1126b/release/simple` (sha256 `fb80903917d6d5f5…`).

## Symptom

`test/01_unit/os/compositor/host_external_content_damage_boundary_spec.spl`
is 0/7.

- Six examples fail with `variable WM_CONTENT_DAMAGE_FULL not found`, raised
  from the spec's own `_damage_frame` helper (line 29).
- The seventh fails with `method render_web_draw_ir_composition_resources_revision
  not found` on `Engine2dCompositorBackend`. That half is already tracked by
  `engine2d_compositor_web_damage_revision_api_missing_2026-11-13`.

`test/01_unit/check/wm_external_content_damage_overlap_contract_spec.spl` is a
source-text contract for the same API (`fn wm_content_frame_damage_plan_valid(`
and a `_wm_content_damage_rects_overlap` helper in
`src/lib/common/ui/window_scene.spl`).

## What the specs expect

On `WmContentFrame`: `producer_revision`, `damage_mode`
(`WM_CONTENT_DAMAGE_NONE` / `_LOCAL` / `_FULL`) and
`damage_resources_accepted`; a validator
`wm_content_frame_damage_plan_valid`; and, in the host compositor, translation
of an accepted LOCAL child plan into parent (browser content) damage, failing
closed to one full parent damage on a skipped revision, unaccepted resources,
overlapping rectangles or an out-of-range coordinate.

## What exists

None of those names is defined under `src/` on release/1.0.0 or on main. They
are absent from the 2026-09-29 transplant tree (`88aac2ffe28`, where both
specs first appear in this history) and from every commit reachable from a
local ref (`git log --all -S` on `window_scene.spl`).

What did land is a different mechanism: the retained-delta path of
`586daf45bba` (`base_content_revision`, `damage_rects`, `damage_pixels`),
where the producer ships changed pixels and the host applies them to the
retained base. It has no damage mode, no producer revision and no
resources-accepted flag.

So this is not a regression that can be bisected: the specs describe a design
whose implementation is not in the repository.

## Decision needed

1. Implement the plan API beside the delta path (the boundary spec is precise
   enough to drive it), stating how a frame that carries both a plan and a
   packed delta is treated; or
2. retire both specs in favour of the delta path's own coverage
   (`test/01_unit/os/hosted/hosted_external_web_frame_spec.spl`).

Until then the spec stays red; it has not been tagged or skipped.
