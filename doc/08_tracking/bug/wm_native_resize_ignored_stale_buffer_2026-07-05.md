# Native OS window resize ignored; compositor keeps stale fixed-size buffer
## Obsolete 2026-09-16 — referenced path(s) gone, e.g. src/os/hosted/hosted_entry.spl:108-151

Reviewed in the 2026-09-16 bug-ledger normalization pass. Kept for history;
the subject is removed, superseded, or duplicated elsewhere in the ledger.

## Status
Open.

## Severity
Medium-High.

## Summary
`src/os/hosted/hosted_entry.spl:108-151` never handles `EVENT_WINDOW_RESIZED=1` or `EVENT_WINDOW_SCALE_FACTOR_CHANGED=7`. Window is created resizable by default, but `HostedWinitBufferBackend` allocates pixel buffer once at create() time (hosted_backend_winit.spl:9-27) with no resize/recreate path. `HostCompositor` is initialized with fixed WINDOW_WIDTH/WINDOW_HEIGHT (hosted_entry.spl:90) for process lifetime.

## Evidence
- **winit_sffi/mod.rs**: Defines EVENT_WINDOW_RESIZED=1 and EVENT_WINDOW_SCALE_FACTOR_CHANGED=7.
- **hosted_backend_winit.spl:9-27**: Single `create()` allocates fixed buffer; no recreate method.
- **hosted_entry.spl:90**: `HostCompositor.new(..., Size(width: WINDOW_WIDTH, height: WINDOW_HEIGHT))` is constant for lifetime.
- **hosted_entry.spl:108-151**: Event loop has no branch for resize/scale-change event types.

## Failure Scenario
Drag-resize the SimpleOS Shared Hosted WM window at OS level → compositor keeps rendering into original 1024x720 buffer while OS frame is different size; content clipped/stretched, mouse coordinates mismapped.

## Next Step
Handle EVENT_WINDOW_RESIZED; allocate new buffer and notify compositor of size change.


## Verification 2026-11-25 (P2 sweep lane) — FIXED (header corrected)

The 2026-09-16 "Obsolete — referenced path(s) gone" banner is inaccurate:
`src/os/hosted/hosted_entry.spl` still exists (now 2144 lines) — but the
defect itself is genuinely gone in the evolved code:

- The event loop now handles both event types this doc names:
  `EVT_RESIZE: i64 = 1` and `EVT_SCALE_FACTOR: i64 = 7`
  (`hosted_entry.spl:162-164`), dispatched at `hosted_entry.spl:1035`
  (`elif kind == EVT_RESIZE or kind == EVT_SCALE_FACTOR:`).
- The compositor is no longer fixed-size-for-lifetime: the resize branch
  calls `comp.resize(physical.width, physical.height)`
  (`hosted_entry.spl:1056`), and `os.compositor.host_compositor_core`
  imports and uses `shared_wm_pixel_buffer_resize` (line 22) — the buffer
  recreate path this doc said was missing.
- A full `HostDisplayTransitionPhase` state machine
  (Requested/AwaitingResize, resize/scale acknowledgment nonces, rollback
  geometry) now governs resize transitions, far beyond the "handle
  EVENT_WINDOW_RESIZED" next step filed here.

Verified by code inspection at release/1.0.0 HEAD; a behavioral run needs a
hosted WM GUI session (OS window drag-resize), which this lane cannot drive.
Status: **RESOLVED** (fixed in the evolved hosted-WM code).
