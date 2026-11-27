# Engine2D compositor: Web damage revision API is called by specs but does not exist

- **ID:** engine2d_compositor_web_damage_revision_api_missing_2026-11-13
- **Status:** OPEN
- **Severity:** P3
- **Found by:** UI batch B, while fixing the 8K frame-switch receipt
  (`web_draw_ir_8k_frame_switch_native_build_timeout_2026-08-11.md`)

## Evidence

`Engine2dCompositorBackend` (`src/os/compositor/compositor_engine2d.spl`) has
no method `render_web_draw_ir_composition_resources_revision` and no fields
`web_effective_damage_mode` / `web_effective_damage_reason`. `git grep` over
`src/` finds no definition of any of the three.

They are used by:

- `test/01_unit/os/compositor/engine2d_frame_switch_receipt_spec.spl:75-86`
  ("replaces prior LOCAL damage with NONE on an exact Web cache hit");
- `test/01_unit/os/compositor/host_external_content_damage_boundary_spec.spl:277-309`;
- `test/01_unit/check/web_8k_retained_surface_payload_contract_spec.spl:20`
  (as a source-text expectation).

Measured on release/1.0.0 `35144b7f5e93`, Rust seed: the receipt spec's fourth
example fails with `method render_web_draw_ir_composition_resources_revision
not found on type object (receiver value: Engine2dCompositorBackend(...))`.

## Expected

A Web-producer entry point that plans damage against the retained revision:
`DAMAGE_PLAN_LOCAL` with non-empty rects when content changes under a new
revision, and `DAMAGE_PLAN_NONE` with reason `web-revision-cache-hit` and no
rects on an exact repeat, as the spec states.

## Not done here

Implementing it means choosing how Web damage planning composes with the
existing `render_draw_ir_composition_resources_revision_damaged` path; that
is a design decision for the compositor owner, not a missing one-liner. The
failing example is left failing.
