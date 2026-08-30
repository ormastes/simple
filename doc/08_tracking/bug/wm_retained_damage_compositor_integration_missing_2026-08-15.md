# WM retained-damage compositor integration missing (specs RED)

**Date:** 2026-08-15
**Status:** RESOLVED 2026-08-15 — implementation landed and runtime-verified: wm_retained_damage_contract_spec 2/2 PASS, wm_multiscale_retained_damage_consumer_contract_spec 4/4 PASS, wm_pixel_pipeline_spec regression 18/18 PASS (load avg ~3, Rust seed binary, SIMPLE_TIMEOUT_SECONDS=540)
**Area:** hosted WM / compositor / retained damage

## Symptom

Two contract specs fail because they assert compositor-side retained-damage
machinery that does not exist anywhere in the tree:

- `test/01_unit/check/wm_multiscale_retained_damage_consumer_contract_spec.spl`
  — `Results: 4 total, 1 passed, 3 failed` (2026-08-15, Rust seed
  `bin/release/x86_64-unknown-linux-gnu/simple`, `SIMPLE_TIMEOUT_SECONDS=540`)
- `test/01_unit/check/wm_retained_damage_contract_spec.spl`
  — `Results: 2 total, 0 passed, 2 failed`

## Evidence

Every one of these anchors greps 0 in the files the specs read:

- `src/os/compositor/compositor_engine2d.spl`: `Engine2dRetainedDamageCalibrationReceipt`,
  `seed_retained_damage_calibration(`, `record_retained_damage_full_sample(`,
  `_ENGINE2D_RETAINED_DAMAGE_MIN_FULL_SAMPLES`, `complete_retained_damage_full_present(`,
  `retained_damage_replay_manifest(`, `retained_damage_resource_manifest(`,
  `admitted_retained_damage_schedule(`, `engine2d_draw_ir_adv_composition_damage_with_images(`,
  `full-seed-warmup`, `owner-token-retained-replay` — all 0 hits.
- `src/os/compositor/host_compositor_core.spl`:
  `val retained_full_started_ns = time_now_nanos()`,
  `executor.complete_retained_damage_full_present(` — 0 hits.
- `src/os/compositor/engine2d_wm_frame_executor.spl`:
  `last_successful_window_rects: [i64]`, `last_successful_background_key: text`,
  `return engine2d_wm_full_damage_plan` — 0 hits; file contains zero
  `retained_damage`/`Calibration` references at all.

`git log -S "Engine2dRetainedDamageCalibrationReceipt" -- src/os/compositor/compositor_engine2d.spl`
returns NOTHING: the implementation never existed in this file's history on
main. The specs were added by `5958de7d4c7` ("wip: integrate simpleos
enhancement work"), which sits directly on top of the tree-wipe/restore pair
`6f86ff32a7d` / `ae55a746719` — the likely mechanism is that the wip commit
carried the specs while the matching compositor implementation was lost with
the wiped tree (or never left the authoring session's worktree).

What DID land: the backend-neutral consumer library
`src/lib/common/ui/render_opt/wm_retained_damage_consumer.spl` (its example —
"keeps the three-scale pyramid backend neutral" — passes).

## Unblock condition

Re-land (or re-author) the compositor integration: calibration receipt +
full-seed warmup in `compositor_engine2d.spl`, present-before-commit ordering
in `host_compositor_core.spl`, and retained old/new extents + background-key
guard in `engine2d_wm_frame_executor.spl`. Then the two specs above must pass
unmodified.

## Related

- Contrast: `test/01_unit/check/wm_external_content_damage_overlap_contract_spec.spl`
  was mere anchor drift after a refactor (behavior intact) and was re-anchored
  same day — that fix is NOT applicable here because the asserted behavior is
  genuinely absent.

## Implementation (2026-08-15, verification pending)

Re-authored the integration to the specs' contract:

- `src/os/compositor/engine2d_wm_frame_executor.spl` — retained old/new
  extents: `last_successful_scene_revision/_window_rects/_background_key` +
  `damage_tiles` pyramid; `retained_scene_damage_plan()` marks BOTH retained
  old extents (5-slot records, `[old + 4] != 0` validity) and current window
  extents on a changed revision; background-identity change and no-prior-frame
  return `engine2d_wm_full_damage_plan` (fail-closed full). Extents committed
  only on the three successful present paths.
- `src/os/compositor/compositor_engine2d.spl` —
  `Engine2dRetainedDamageCalibrationReceipt` + full-seed warmup lifecycle:
  `seed_retained_damage_calibration()` (owner-issued, idempotent),
  `record_retained_damage_full_sample()`,
  `complete_retained_damage_full_present()` (host post-present commit),
  `admitted_retained_damage_schedule()` (admission token; reasons
  `immediate-mode-no-replay-receipt` / `presenter-full-seed-unpresented` /
  `full-seed-warmup` / `owner-token-retained-replay`), replay/resource
  manifests, and `render_draw_ir_composition_from_retained_damage` now gated
  on the admitted schedule with full-composition fallback feeding calibration.
- `src/os/compositor/host_compositor_core.spl` — seeds at frame entry;
  `val retained_full_started_ns = time_now_nanos()` before blit, and
  `executor.complete_retained_damage_full_present(...)` strictly AFTER
  `self.pixel_backend.present()`.

All 44 spec string/ordering assertions verified statically against the edited
sources. Deferred verification (run after the lock lifts):

```
SIMPLE_TIMEOUT_SECONDS=540 bin/simple test test/01_unit/check/wm_retained_damage_contract_spec.spl
SIMPLE_TIMEOUT_SECONDS=540 bin/simple test test/01_unit/check/wm_multiscale_retained_damage_consumer_contract_spec.spl
SIMPLE_TIMEOUT_SECONDS=540 bin/simple test test/02_integration/rendering/wm_pixel_pipeline_spec.spl  # regression
```
No PASS is claimed until those run.
