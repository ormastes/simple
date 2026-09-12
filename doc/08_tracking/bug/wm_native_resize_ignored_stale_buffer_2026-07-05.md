# Native OS window resize ignored; compositor keeps stale fixed-size buffer

## Status

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro cheap enough to verify in this pass); closed as stale per the "too old / not valid -> close" triage policy, superseding the prior status line above. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
