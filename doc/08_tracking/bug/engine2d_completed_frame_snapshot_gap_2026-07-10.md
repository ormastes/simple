# Engine2D Has No Completed-Frame Evidence Snapshot

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
