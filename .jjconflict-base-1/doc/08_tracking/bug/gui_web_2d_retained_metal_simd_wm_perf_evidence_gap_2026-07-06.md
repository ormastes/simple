# GUI Web 2D retained Metal/SIMD WM perf evidence gap

- **Date:** 2026-07-06
- **Status:** open
- **Severity:** high
- **Area:** GUI Web 2D, Engine2D Metal/SIMD, hosted WM, SimpleOS/QEMU WM

## Summary

The current WM showcase path now has filesystem-launched child evidence for
button/toggle/slider events and tick-driven redraw, and the SimpleOS/QEMU WM
fullscreen check proves framebuffer enter/exit rendering. That does not yet
prove the retained GUI Web 2D Metal/SIMD performance target across hosted WM
and SimpleOS WM.

For the optimization gate, a valid claim still needs a retained evidence row
with viewport, backend, source revision, readback mode, p50/p95 timing, memory
or RSS budget, fallback state, and checksum/readback proof. Existing bugs cover
several underlying causes, including interpreted Engine2D mirror cost and CSS
WM scene render cost, but there is no single retained host/SimpleOS WM evidence
gate that shows the Metal/SIMD path is fast enough and not falling back.

## Expected

- Hosted WM launches the GUI showcase from the filesystem, not embedded in the
  WM, and records retained-frame render timing for `software`, `cpu_simd`, and
  `metal` where available.
- SimpleOS/QEMU WM records the equivalent fullscreen retained render evidence
  through the shared app/WM protocol, with SimpleOS-specific adapter/config
  differences only.
- Evidence includes source revision, viewport, backend, readback source,
  fallback status, p50/p95 timing, memory/RSS budget where available, and a
  checksum or framebuffer delta proof.

## Actual

- Filesystem WM-client interaction evidence passes for event propagation and
  redraw:
  - button/toggle/slider probe: `event_seq=6`, `button_count=1`,
    `switch_on=false`, `slider_value=93`, `frame_seq=2`
  - tick probe: `event_seq=1`, `progress_value=64`, `frame_seq=2`
- SimpleOS/QEMU fullscreen evidence passes:
  - command:
    `BUILD_DIR=build/simpleos_wm_fullscreen_goal_2026_07_06 REPORT_PATH=doc/09_report/simpleos_wm_fullscreen_goal_2026-07-06.md sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs`
  - result: `simpleos_wm_fullscreen_status=pass`,
    `size=1024x768`, `changed_bytes=2273500`
- There is still no retained Metal/SIMD WM perf row proving p50/p95 and
  fallback state across host and SimpleOS.

## Related Existing Bugs

- `doc/08_tracking/bug/engine2d_interpreted_mirror_dominates_render_2026-07-03.md`
- `doc/08_tracking/bug/web_presenter_interp_perf_2026-07-05.md`
- `doc/08_tracking/bug/wm_scene_css_render_perf.md`
- `doc/08_tracking/bug/engine2d_fast_metal_clip_poisons_gpu_readback_2026-07-03.md`

## Recommended Fix

1. Add a retained WM Web 2D perf evidence script under `scripts/check/` that
   launches the showcase app from the filesystem through the shared WM protocol.
2. Record per-backend retained render timing and readback provenance for hosted
   WM, including `cpu_simd` and `metal` on macOS/aarch64.
3. Record the SimpleOS/QEMU equivalent through the fullscreen WM demo path,
   using platform adapter/config differences only.
4. Fail honestly when Metal resolves to software or when the evidence is
   headless/cache-only instead of retained live-frame rendering.

## Sidecar Status

Multiple `gpt-5.3-codex-spark` sidecar launches were attempted for Metal,
SIMD/aarch, hosted WM, and SimpleOS/QEMU lanes. Each Spark worker failed with
the usage-limit error, so this blocker was filed from the main rollout rather
than from a completed Spark sidecar.
