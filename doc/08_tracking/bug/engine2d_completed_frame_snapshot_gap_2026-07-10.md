# Engine2D Has No Completed-Frame Evidence Snapshot
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


---

## Triage note 2026-11-25 (release/1.0.0 ledger pass)

Still a live feature-gap, not a stale entry. Verified by code inspection at
HEAD: the Engine2D facade (`src/lib/gc_async_mut/gpu/engine2d/engine.spl`,
`engine2d_api.spl`) has no completed-frame snapshot API — the only "snapshot"
mentions are unrelated (an offscreen compositing fast path and a Metal
readback comment). The `completed_frame_generation` tracking that does exist
lives in `src/os/compositor/compositor_gpu_surface_owner.spl` (compositor
surface owner, not the Engine2D facade) and is not consumable by
`BackendRenderRecord` (`src/lib/common/renderdoc/backend_render_record.spl`).

Classification: SKIP for a bounded P2 fix — the required fix is a designed,
opt-in, backend-owned snapshot seam across the Engine2D facade plus a record
adapter change; that is feature/design work with owner-decision surface, not a
clear-root-cause patch. The 2026-09-16 "needs owner triage" header remains
accurate.
