# WM Retained Frame Switching Evidence — 2026-08-11

## Result

PASS for production WM idle-frame switching and same-scene dynamic damage on
the persistent local Engine2D executor. Physical scanout performance remains
open.

`Engine2dWmFrameExecutor.render()` now computes a retained input identity before
window filtering, resource resolution, DrawIR composition, rasterization, batch
submission, readback, or presentation. A frame is reusable only after a prior
successful render with the same:

- scene and taskbar revisions;
- clock label;
- ordered content-frame count and identities;
- content revision, dimensions, checksum, hierarchy, and offsets;
- renderer/material/theme provenance.

Pixel arrays are not duplicated in retained state. Their already-validated WM
checksum is the byte identity. Failed or rejected frames never populate the
successful-frame key.

Content changes mark visible window extents including bounded
chrome/shadow spill; taskbar or clock changes mark the taskbar. A persistent
64-pixel dirty-tile pyramid emits deterministic, non-overlapping rectangles
with a 60% full-frame threshold and 64-rectangle cap. Changed scene revisions
now mark both retained and current visible window extents, allowing moves,
focus/z-order changes, additions, removals, and minimization to replay through
exact clips. A changed viewport/background identity remains conservative FULL;
translucency, offscreen surfaces, and parent sampling also remain FULL.

The new retained old/new-extent source contract passes 2/2. Two behavioral
examples were added for moved-window LOCAL planning and background-change FULL
fallback. The current self-hosted integration runner exits after session setup
without emitting their verdict, so those examples are pending executable
admission and are not included in the historical 8-example PASS below.

## Verification

```sh
SIMPLE_TIMEOUT_SECONDS=180 bin/simple test \
  test/01_unit/os/compositor/engine2d_wm_frame_executor_spec.spl \
  --mode=interpreter --no-session-daemon
```

Verdict: 8 examples, 0 failures. The production-object scenario creates a
persistent software Engine2D and framebuffer, then verifies:

1. the first frame returns success and `retained_frame_render_count == 1`;
2. an identical frame returns success, leaves render count at 1, and increments
   `retained_frame_reuse_count`;
3. changing the clock identity produces one LOCAL damage frame;
4. independent scene, taskbar, clock, content-revision, and checksum changes
   all reject retained reuse;
5. the entire damaged framebuffer is pixel-identical to a fresh full-frame
   oracle, with zero mismatches.

The parity oracle also caught stale retained state: the legacy full executor
did not return its updated `Engine2D` value. Local WM frames now use the
state-returning composition seam for both FULL and LOCAL plans.

## Honesty Boundary

The settled frame performs no DrawIR construction, raster work, GPU submission,
readback, or framebuffer presentation. This is the intended frame-switching
path and is viewport-size independent after the first successful frame.

It does not prove 8K/80 dynamic rendering. That still requires same-run
p50/p95/RSS/checksum evidence on CPU, Vulkan, and actual SimpleOS scanout.
