# Engine2D Has No Completed-Frame Evidence Snapshot
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Status

Open; blocks truthful binding of `BackendRenderRecord` to live Engine2D frames.

## Evidence

`Engine2D.read_pixels_with_source()` delegates to the active backend. Vulkan
returns a positive device handle only while dirty (before `present()`), while
the post-present cached readback has handle `0`. The public facade has no
frame-completion flag, backend handle, transition list, or backend-owned
pipeline/resource snapshot.

## Required Fix

Add an opt-in, backend-owned completed-frame snapshot to the Engine2D façade.
It must carry actual requested/selected backend, native/translation state,
positive device handle when applicable, frame-complete state, readback source,
and detailed command/pipeline/resource/transition data. The record adapter
must consume that snapshot; it must not infer completion from `present()` or
caller-provided fields.

## Impact

The common record/diff validator remains verified, but no live Engine2D record
is accepted until this seam exists. This prevents CPU mirrors or pre-present
device reads from being represented as completed hardware frames.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
