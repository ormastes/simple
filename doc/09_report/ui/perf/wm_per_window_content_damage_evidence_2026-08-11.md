# WM per-window content damage evidence — 2026-08-11

Status: **MECHANISM IMPLEMENTED; FOCUSED SPEC PASS**

## Change

`Engine2dWmFrameExecutor` now retains one exact content-subtree identity per
scene window. A content-only frame update marks only the canonical content
rectangle of the affected window. Nested content frames resolve through their
parent chain to the owning top-level window. Unrelated windows, title bars,
borders, and shadows are no longer invalidated merely because another content
frame changed.

The production admission path reuses those per-window identities to form the
whole-frame retained key. It no longer serializes every content field once for
the global key and again for damage classification. Ownership is resolved
frame-major (one parent-chain walk per frame), rather than repeating that walk
for every window.

The existing conservative gates remain unchanged: scene revision changes take
the full-frame path; taskbar/clock changes mark the taskbar; invalid or large
plans retain the damage planner's full-frame fallback.

## Correctness gate

Added an exact identity isolation case to
`test/01_unit/os/compositor/engine2d_wm_frame_executor_spec.spl`: changing a
nested child must alter its owning window key and leave a second window's key
identical.

Command attempted once:

```text
bin/release/x86_64-unknown-linux-gnu/simple test test/01_unit/os/compositor/engine2d_wm_frame_executor_spec.spl --mode=interpreter
```

The first attempt was terminated by the default 60-second CPU guard before
execution. After the implementation changed, one bounded verification was run
with `SIMPLE_TIMEOUT_SECONDS=180`.

Result: **PASS — 9 examples, 0 failures** (36.098 seconds reported test
duration). The nested-content ownership isolation and persistent-frame pixel
parity cases both passed.

No 8K/80 performance claim is made from this mechanism-only change.
