# WM content damage-plan API: specified by two specs, never landed

Status: fixed (2026-11-27 on `work/w4-6-wm-compositor-damage-20261127`).
Originally measured 2026-11-26 on release/1.0.0 `f2f5776b73f`, seed
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

## Resolution (Option 1 — Implemented 2026-11-27)

Implemented Option 1 (landing the damage-plan API alongside the existing packed-delta path):
- `src/lib/common/ui/window_scene.spl`: exported `WM_CONTENT_DAMAGE_NONE` (`0`), `WM_CONTENT_DAMAGE_LOCAL` (`1`), `WM_CONTENT_DAMAGE_FULL` (`2`); added defaulted fields `producer_revision: i64 = 0`, `damage_mode: i64 = WM_CONTENT_DAMAGE_FULL`, `damage_resources_accepted: bool = false` on `WmContentFrame`; added `_wm_content_damage_rects_overlap`, `_wm_content_damage_rect_in_bounds`, and `wm_content_frame_damage_plan_valid`.
- `src/os/compositor/simple_web_window_renderer.spl`: extended `simple_web_external_content_frame` and `simple_web_external_content_frame_with_theme_receipt` with optional damage-plan parameters (`producer_revision`, `damage_mode`, `damage_rects`, `damage_resources_accepted`).
- `src/os/compositor/compositor_engine2d.spl`: added `engine2d_revision_result_payload_cacheable`, `revision_cache_surface_valid`, `web_effective_damage_*`, and `render_web_draw_ir_composition_resources_revision(...)` with 8K payload elision and `composition_damage_between` + `web_draw_ir_consume_damage`.
- `src/os/compositor/host_compositor_core.spl`: kept packed-delta handling (`frame.base_content_revision != 0 or frame.damage_pixels.len() != 0`) distinct from damage-plan admission, translating valid `LOCAL` plans into clamped parent rects, honoring clean `NONE` updates without false damage, and failing closed to one full parent rect on invalid plans, skipped revisions, unaccepted resources, overlapping rects, or out-of-bounds coordinates; added `has_pending_damage()`.
- Removed stale `# @tag:in-development` headers from `test/01_unit/os/compositor/host_external_content_damage_boundary_spec.spl` (updating Example 7's theme selector from removed `"glass_dark"` to active-or-default theme) and `test/01_unit/check/wm_external_content_damage_overlap_contract_spec.spl`.

### Verification (`wa3_shared_bin/simple.exe test ... --mode=interpreter`, `SIMPLE_ASSET_ROOT=C:\dev\simple`)
- `test/01_unit/os/compositor/host_external_content_damage_boundary_spec.spl`: 7/7 passed (`outcome=OK`).
- `test/01_unit/check/wm_external_content_damage_overlap_contract_spec.spl`: 2/2 passed (`outcome=OK`).
- `test/01_unit/os/compositor/engine2d_frame_switch_receipt_spec.spl`: 5/5 passed (`outcome=OK`).
- `test/01_unit/check/web_8k_retained_surface_payload_contract_spec.spl`: 2/2 passed (`outcome=OK`).
- `test/01_unit/os/compositor/host_content_frame_admission_spec.spl`: 1/1 passed (`outcome=OK`).
- `test/01_unit/os/compositor/simple_web_window_renderer_spec.spl`: 28/28 passed (`outcome=OK`).
- `test/01_unit/os/compositor/external_web_frame_theme_identity_guard_spec.spl`: 4/4 passed (`outcome=OK`).
- `test/01_unit/os/compositor/host_compositor_pending_damage_spec.spl`: 2/2 passed (`outcome=OK`).
- `test/01_unit/os/compositor/engine2d_compositor_revision_generation_spec.spl`: 2/2 passed (`outcome=OK`).
- Pre-existing baseline failures outside this change: `engine2d_compositor_revision_cache_spec.spl` 7/8 (example 5 hits duplicate `revision_cache_local_fixture` in spec lines 24/65), `hosted_external_web_frame_spec.spl` 3/4 (example 1 hits unescaped CSS `{...}` at spec line 74; all 3 compositor/delta examples pass), `hosted_web_none_damage_present_gate_source_spec.spl` 0/1 (checks untouched `src/os/hosted/hosted_entry.spl`).
