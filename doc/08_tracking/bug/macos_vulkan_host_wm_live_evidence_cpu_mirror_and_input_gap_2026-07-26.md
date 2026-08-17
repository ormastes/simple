# macOS Vulkan Host-WM Evidence Uses a CPU Presentation Mirror and Synthetic Commands

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

## Status

**OPEN — fail closed.** This is a source-path audit only. No host-WM live
Vulkan launch, capture, or PASS was attempted from this worktree.

## Scope

The affected gate is
`scripts/check/check-wm-production-fullscreen-evidence.shs` when
`SIMPLE_GUI_BACKEND=vulkan`. The gate must remain blocked behind the Vulkan
2D, web, and GUI live gates and must not be used to establish Vulkan host-WM
parity until the acceptance criteria below are implemented and independently
verified.

## Exact producer and consumer paths

1. `src/os/hosted/hosted_entry.spl::main` creates a
   `HostCompositor` with `HostCompositor.new_headless` and an
   `Engine2dCompositorBackend` selected from `SIMPLE_GUI_BACKEND`, then passes
   both into `_run_hosted_wm`.
2. `HostCompositor.render_frame_engine2d` in
   `src/os/compositor/host_compositor_core.spl` accepts
   `Engine2dDrawIrAdvResult.pixels` and copies them into
   `SharedWmPixelBufferBackend` through `self.pixel_backend.blit_pixels(...)`.
3. The hosted entry presents and writes all evidence captures from
   `comp.pure_simple_pixel_buffer()` through
   `hosted_winit_present_pure_simple_pixels(...)` and
   `host_wm_evidence_write_capture(...)`.
4. `src/os/hosted/hosted_wm_evidence.spl` serializes that supplied pixel array
   directly to PPM and carries no typed capture-origin, device identity,
   readback handle, or per-frame binding to the array.
5. The shell gate separately greps log strings from
   `Engine2dCompositorBackend.frame_provenance()` for `backend=vulkan`,
   `source=device_readback`, a positive handle, and a checksum. It compares
   those checksum values with the PPM checksum, but the snapshot contract
   simultaneously requires `render.backend == "simple-2d-winit-buffer"` and
   `render.readback == "presented-pixel-buffer"`.

## Evidence contradiction

The shell wrapper can therefore describe a Vulkan device-readback receipt
while its qualifying capture/snapshot producer is the CPU-side shared pixel
buffer. A checksum equality is useful integrity evidence, but does not make
the PPM producer a typed same-frame device-readback capture or rule out a
substituted CPU mirror. The current snapshot schema also cannot expose enough
information to prove that the capture bytes originated from the validated
Vulkan readback handle and frame.

The source comments explicitly call the hosted presentation buffer a "pixel
mirror". This path must not be relabeled as a direct Vulkan presentation path
or accepted as a workaround for the no-CPU-mirror evidence rule.

## Event-causality gap

`SIMPLE_WM_EVIDENCE_INPUT_FIFO` is a regular command-file protocol, not an OS
input injector. The checked commands (`tab`, `pointer`, `left`, `f11`, and
others) call compositor/fullscreen helpers directly in the evidence branch.
They do not produce and correlate native focus, keyboard, text, pointer, and
click events from the launched window PID. The receipt records counters but
not a command/action identity, native event sequence, or before/after frame
identity sufficient to establish causal ordering.

## Additional gate gaps

- The app loop has an independent 300-second process bound, and the wrapper
  applies `WM_EVIDENCE_TIMEOUT_SECS` to each wait separately. Neither is a
  wrapper-owned launch-to-final aggregate deadline, and the acceptance record
  does not report an aggregate elapsed time or prove every phase completed
  inside one bounded interval.
- It records a shell PID internally but does not publish or validate a
  capture/window identity bound to that PID, and it has no launch-time or
  phase-time RSS ceiling.
- `Engine2dCompositorBackend.font_provenance()` logs a font identity and target,
  but the gate does not snapshot or validate a selected vector-face identity,
  a `FontRenderer`/`FontRenderBatch` receipt, 300-DPI configuration, exact
  physical-pixel geometry, or cold/warm font-cache evidence.

## Required qualifying acceptance gate

Before a host-WM Vulkan PASS, implement a dedicated evidence contract that:

1. launches one manifest-attested native artifact and records its PID, exact
   native window number/owner PID, executable identity, and device identity;
   the discovered visible macOS window must retain that PID binding for every
   capture and event phase;
2. enforces one 180-second launch-to-final monotonic deadline and a 20-second
   maximum for each readiness/input/capture/transition phase; records aggregate
   and per-phase elapsed milliseconds; and rejects before starting any command
   whose remaining global budget cannot contain its phase deadline;
3. enforces a 1,048,576-KiB maximum RSS for the launched PID, samples at least
   every 250 ms while waiting, and records peak RSS plus the timestamp/phase of
   every sample and any breach;
4. produces windowed, fullscreen, and restored visible native-window captures
   bound to that PID/window. Each decoded capture must be correlated to the
   exact completed Vulkan device-readback frame, device, positive handle, byte
   count, and checksum; CPU-rendered, upload-only, or untyped mirror output is
   not an accepted capture authority;
5. binds each capture, snapshot, device handle, checksum, and presentation
   revision to one monotonic frame identity and rejects mismatches;
6. injects native focus, key-down/key-up, text, pointer movement, and
   click/down/up events into the launched PID, then records ordered native
   event receipts and an observable state/pixel delta for each required
   interaction;
7. validates decoded-pixel semantics and bounds: at least one visible internal
   window, its titlebar/content fully within the 3840x2160 surface, a visible
   taskbar within bounds, non-background content in both regions, exact
   maximize geometry, exact restore geometry, and a pixel/state delta caused
   by the correlated taskbar/window interaction;
8. requires the plan's exact 3840x2160 physical surface at 300x300 DPI,
   canonical Draw IR text through `FontRenderer`/`FontRenderBatch`, a nonempty
   selected vector-face identity, a 24-point glyph height of 100 physical
   pixels, and cold/warm font-cache receipts; and
9. fails closed for CPU mirror, software fallback, synthetic handle, missing
   provider, stale artifact, missing phase artifact, duplicate/stale nonce,
   non-monotonic frame, deadline breach, or RSS breach.

Only a fresh live run satisfying all nine items may advance host-WM Vulkan to
PASS; it must precede QEMU WM and Metal WM work.

## Bounded static probes

- `sh -n scripts/check/check-wm-production-fullscreen-evidence.shs`: PASS.
- Source trace confirmed the producer/consumer paths above.
- No compiler, native-build, live launch, or screenshot probe was run.
