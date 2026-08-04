# gpu-first present default publishes an EMPTY frame when the GPU lane declines

- **Filed:** 2026-08-04
- **Status:** FIXED in the presenter — but see "Correction to the attribution"
  below: the 12/17 gate failure was NOT caused by this code path.
- **Severity:** high — the decline branch really could publish an empty frame
- **Owner module:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_engine2d_presenter.spl`
- **Fix owner:** claimed + landed 2026-08-04

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

## Fix

- **Commit:** `fix(web-gpu): make the gpu-first decline actually paint the frame on the CPU` (2026-08-04)
- **Change:** the `economics.fill_op_count == 0 or economics.fill_pixels == 0`
  decline branch in `_present_gpu_first` no longer mirrors the unusable GPU
  frame via `_cpu_mirror_for_frame`. It now calls
  `simple_web_layout_render_html_readback_paint(html, width, height, backend_name, false)`
  — the identical call the explicit-CPU-backend / unknown-backend decline a few
  lines above already makes — so a lane that cannot complete falls back and
  actually PRODUCES the frame. The decision string is unchanged; it was already
  honest.
- **Contract pinned:** `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_gpu_first_present_decision_spec.spl`
  landed with the fix (5/5). It pins the per-frame decision-string honesty
  contract: degenerate surface, explicit CPU backend, unknown backend, device
  provenance required for any offload claim, three-mode env routing.

## Correction to the attribution (measured 2026-08-04)

The root cause described above is real — mirroring a degenerate GPU frame does
publish an empty buffer — but it is **not** what produced the `12 passed, 5
failed` gate result, and the gate was never red at `3ddd017c87d` itself.
Measured in a pristine `git worktree` at that exact base, with the shared
working copy's uncommitted changes excluded:

| tree | presenter | Results |
|---|---|---|
| clean worktree @ `3ddd017c87d` | **base (no fix)** | `17 total, 17 passed, 0 failed` |
| clean worktree @ `3ddd017c87d` | with this fix | `17 total, 17 passed, 0 failed` |
| clean worktree @ `5c03d99d65c` | with this fix | `17 total, 17 passed, 0 failed` |
| shared working copy | with this fix | `17 total, 12 passed, 5 failed` |

The decline branch was exercised in every one of those runs (the
`[web-gpu-paint-decision] ... reason=cpu-ground-truth-required:cpu-paint-required`
marker appears 3x, 1x, 2x and 3x respectively), so the green runs are not
vacuous — the branch this fix rewrites really did execute and really did
publish a full-size frame.

What actually reddens the gate is the **shared working copy**, which carries
~6,300 lines of another session's uncommitted, in-flight Engine2D/Vulkan work
(`src/lib/gc_async_mut/gpu/engine2d/engine.spl`, `vulkan_session.spl`,
`backend_vulkan*.spl`, `draw_ir_*`). Because these are `.spl` libraries executed
from source, any spec run in that tree picks them up.

The decisive tell is the fifth failing example, *"direct Engine2D lane render of
the cpu oracle is bit-exact with real provenance"* → `expected nil to be greater
than 0`. Its helper `_render_lane_direct` calls `Engine2D.create_requested_backend`,
`present()` and `read_pixels_with_source()` **directly and never touches the
presenter at all** — the nil is `readback.backend_handle` coming back from the
Vulkan backend. No change to this file can affect that assertion. The four
`expected 0 to equal 4800` failures are the same backend returning an empty
readback through `present_layout_pixels_with_engine2d_readback`, which the CPU
fallback also has to traverse.

Contributing factor in that tree: heavy host load (19 concurrent `simple test`
processes plus a 32-thread build) drives `[web-style-producer] budget-break`,
which is what degenerates the GPU frame in the first place. That is the
condition under which the mirroring defect above becomes observable — which is
why the fix is still worth landing: it removes the empty-frame failure mode
permanently instead of leaving it latent behind a load-dependent trigger.

**Corroboration:** that in-flight Engine2D work landed independently as
`28288f98102 fix(engine2d): stop a font-poisoned Vulkan lane publishing a
partial frame` while this fix was being verified — the same failure mode, fixed
in the layer that actually owned it.

**Follow-up owed elsewhere:** the Vulkan `read_pixels_with_source()` nil
`backend_handle` / empty readback belongs to the Engine2D lane, not here. It
must not be closed by this bug.

## Still open (deliberately not fixed here)

The "Adjacent case to cover" above — the `gpu-full` / `gpu-partial` prefix is
still derived from `economics.residual_pixels` rather than from
`readback.source`, so the prefix can over-claim while the `source=` field stays
honest. Left out because binding the prefix to the readback source changes the
decision-string vocabulary the parity and showcase gates assert against; that is
not a small obviously-correct edit and deserves its own lane.
