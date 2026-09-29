# Pure Simple Vulkan image-source pool (2026-09-10)

Status: implemented; runtime GPU performance row pending admitted provider
authority.

## Scope

The production Pure Simple Engine2D path is
`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl` ->
`backend_vulkan_helpers.spl` -> the checked Vulkan SFFI.  The existing batched
image-composite path allocated one storage buffer, copied pixels into it,
retained it through the frame fence, and freed it for every image draw.  The
2026-09-06 Linux comparison identifies this class of per-operation marshalling
and allocation as a dominant cost, but the current Stage-2/provider gate does
not permit a new hardware timing claim.

Canonical `Engine2D.create_vulkan_backend` and requested Vulkan construction
enable frame batching, so this is the production image-composite path rather
than a benchmark-only adapter.

## Change

When `frame_batching_enabled` is true, each surface now owns a bounded pool of
up to the existing 256 pending-dependency slots.  A source buffer is reused
only when it is not present in the current pending table, which is cleared only
after the command was discarded before submission or authoritative fence/device
idle completion.  Pool reuse also requires the exact retained session device,
session generation, and surface framebuffer identity.  The source remains
bound to a fresh per-draw descriptor until the common frame flush, then becomes
reusable.  Unknown completion quarantines the pending pooled resources and
drops the pool; shutdown frees the pool after recovery.  Batching-disabled
calls retain the old transient allocation/free behavior.

When all 256 slots are pending, the caller takes the same mid-frame blocking
flush that the pre-pool dependency-table limit already required. Allocation
failure, owner mismatch, and a completed undersized slot do not add a flush:
the undersized slot is replaced in place and other failures remain fail-closed.

## Structural before/after evidence

| Path | Before | After |
|---|---|---|
| batched image draw | 1 Vulkan source allocation + 1 free per draw | 1 allocation per pool slot, then reuse after fence |
| CPU-to-GPU upload | 1 full image upload per draw | unchanged: 1 full image upload per draw |
| pending dependency ownership | source freed by release path | pooled source retained; descriptor still released per frame |
| unknown completion | pending source quarantined | pending source plus every pooled source quarantined, pool discarded |
| batching disabled | transient source allocation/free | unchanged |
| pool bound | none | <= 256 source slots, matching pending table; completed undersized slots are replaceable |

The counters `image_source_pool_reuse_count`,
`image_source_pool_allocation_count`, `image_source_pool_replacement_count`,
`image_source_upload_count`, and `image_source_upload_bytes` are owner-side
structural observability only; they do not imply device execution or a
performance pass.

## Verification

- Static contract: `test/01_unit/check/vulkan_engine2d_image_source_pool_contract_spec.spl`
- Static contract execution: WARN. The single bounded interpreter attempt was
  rejected by the existing test-runner outer-budget timeout before assertions
  could complete; no runtime PASS is claimed.
- O3 source analysis: PASS for both changed Pure Simple source files. It
  completed without syntax failure and reported only advisory opportunities.
- Runtime/hardware timing: not run; the admitted Pure Simple Stage-2/provider
  gate remains blocked and this lane must not fabricate a GPU measurement.
- Chrome comparison: not run; it is outside this bounded change.
