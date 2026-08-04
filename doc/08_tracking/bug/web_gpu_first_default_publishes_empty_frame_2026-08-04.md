# gpu-first present default publishes an EMPTY frame when the GPU lane declines

- **Filed:** 2026-08-04
- **Status:** OPEN
- **Severity:** high — regresses the DEFAULT web present path on `main`
- **Owner module:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_engine2d_presenter.spl`
- **Fix owner:** unclaimed

## Symptom

`test/02_integration/rendering/web_engine2d_gpu_offload_parity_spec.spl`, the
regression gate for the web GPU offload lane, went from 17/17 to:

```
Results: 17 total, 12 passed, 5 failed
```

Failing examples and their matcher output:

| Example | Failure |
|---|---|
| nested boxes-and-borders scene matches between cpu oracle and offload lane | `expected 0 to equal 4800` |
| solid-background scene is dominated by the CSS color and parity holds | `expected 0 to equal 4800` |
| scrolled content shifts correctly and matches on the offload lane | `expected 0 to equal 4800` |
| explicit gpu-paint readback on the lane matches the cpu truth | `expected 0 to equal 4800` |
| direct Engine2D lane render of the cpu oracle is bit-exact with real provenance | `expected nil to be greater than 0` |

`4800` is the expected pixel count (80x60). The lane returned an **empty**
buffer — not a wrong pixel, no pixels at all.

## Root cause

The gpu-first default lane (`SIMPLE_WEB_GPU_PAINT` unset routes
`simple_web_layout_render_html_readback` through `_present_gpu_first`) declines
to CPU on these scenes, which it reports honestly:

```
[web-gpu-paint-decision] backend=vulkan gpu-first:cpu-raster:offloaded=none:cpu=full-frame:reason=cpu-ground-truth-required:cpu-paint-required
```

But the decline branch does not re-run the real CPU renderer. It mirrors the
GPU frame it already failed to use:

```simple
val pixels = _cpu_mirror_for_frame(frame, frame.base)
return _WebGpuFirstPresent(
    readback: present_layout_pixels_with_engine2d_readback(pixels, width, height, normalized_backend, frame.base),
    decision: decision)
```

`_cpu_mirror_for_frame` returns `frame.fb` only when it is full-size, otherwise
`_simulate_fill_ops(frame, base)`, which allocates `[base; frame.width *
frame.height]`. When `simple_web_layout_render_html_gpu_frame` yields a
degenerate/failed frame (zero dimensions, zero fill ops), both arms produce an
empty buffer, so the "honest CPU fallback" publishes nothing.

The pre-change code took the genuine CPU path in this situation:

```simple
simple_web_layout_render_html_readback_paint(html, width, height, backend_name, web_gpu_paint_enabled())
```

## Why this matters beyond the failing gate

This is the exact case the GPU-first policy exists to prevent: a lane that
cannot complete must fall back and say so, **not publish a partial result**.
The decision string is honest; the pixels are not. A consumer that trusts the
readback gets an empty frame with a `cpu-raster` label. The probe (device
creation + device-derived readback source) works correctly — the defect is in
the decline branch's recovery, not in the capability detection.

## Fix direction

The decline branch must call the real CPU renderer
(`simple_web_layout_render_html_readback_paint(html, width, height,
backend_name, false)`) rather than mirroring the unusable GPU frame — the same
call the explicit-CPU-backend and unknown-backend branches already make a few
lines above. Add a regression example asserting the declined lane still returns
`width * height` pixels.

## Adjacent case to cover

The `gpu-full` / `gpu-partial` prefix in the decision string is derived from
`economics.residual_pixels`, not from the readback source. If
`Engine2D.create_requested_backend` succeeds but the device yields a CPU-sourced
readback, the string can read `gpu-first:gpu-full:...:source=cpu_mirror` — the
`source` field stays honest but the prefix over-claims. Bind the prefix to the
readback source.

## Evidence

- Failing run (seed `bin/simple test`): `Results: 17 total, 12 passed, 5 failed`
- Decision markers captured in the same run (quoted above), 3 occurrences.
- The gpu-first lane itself is proven working on a real device elsewhere in the
  same session: `gpu-first:gpu-full:offloaded=rect_fill:2ops/1760px:cpu=none:source=device_readback:handle=1:device_identity=134816422716128`
