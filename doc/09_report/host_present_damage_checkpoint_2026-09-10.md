# Hosted present damage checkpoint

Status: **WARN — source fix connected; executable verification TEST_BLOCKED.**

The Pure Simple host previously used the number of dirty rectangles as part of
its present acknowledgement identity, then cleared every rectangle on commit.
A new event while a host-buffer present was pending therefore rejected a valid
older receipt when the count grew. Clear/readd at the same count could instead
let that older receipt clear replacement damage. Spatially identical damage is
not the same event generation.

`DirtyRegion` now exposes one owner-issued epoch/count prefix checkpoint.
Appends preserve the prefix; clear and retirement revoke old checkpoints
through a non-wrapping epoch. `HostCompositor` captures that value before
provider entry, validates that checkpoint with the existing
surface/device/provider/scene and external
revision checks, then retires only the captured rectangles after the matching
present receipt. Counts not issued for the active epoch fail closed instead of
retiring an arbitrary shorter prefix. Overlapping later rectangles remain
dirty. The checkpoint adds constant-size scalar state; retiring copies only the
remaining rectangle metadata and does not serialize DrawIR, copy framebuffer
pixels, wait for the GPU, or read back device memory.

The host remains the single mutation owner during receipt validation and
commit. No callbacks or device operations occur between checkpoint validation,
external-revision commit, and prefix retirement. The epoch is host bookkeeping,
not a provider-issued resource capability. This patch does not admit concurrent
mutation from another thread or add a GPU submission queue.

## Verification scope

- Six direct owner scenarios in
  `test/01_unit/os/compositor/dirty_rect_checkpoint_spec.spl`: newer overlapping
  damage, clear/readd, duplicate retirement, malformed checkpoints, empty prefix,
  and exhaustion.
- Two real software Engine2D/HostCompositor call-path scenarios in
  `test/01_unit/os/compositor/host_compositor_pending_damage_spec.spl`: delayed
  acknowledgement preserves the successor damage, and stale replacement
  rejection preserves pending work. Presenter sequence values are injected
  control-flow observations, not native window evidence.
- The existing GUI source contract now requires prefix validation/retirement
  instead of rectangle-count equality. A source assertion is not execution.
- `git diff --check` and no-index whitespace checks for the three new files
  passed. The patch adds no environment or process-runtime access; these are
  source-hygiene observations only.
- No deployed Darwin runtime exists in the PR worktree. The sibling root's
  available compiler receipt is `simpleos-arm64-compiler-receipt-v1`, identifies
  `simple-bootstrap 1.0.0-beta`, and records native compiler smoke only. It does
  not admit a general `test`/SPipe runner. No Rust seed or new bootstrap was used.

## Production async blocker, still present

`src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl` still reports managed range
binding unsupported. `VulkanSession` still obtains opaque runtime-managed
resources, with no atomic operation exporting the existing context and its
resource membership to an async owner. `vulkan_sffi_present_buffer[_regions]`
still returns synchronous scalar status, with no separately pollable source
release token. The existing `submit_no_wait` quarantine route cannot replace
that missing ownership protocol. This is absent functionality, not just absent
test tooling.

Implementing the selected bridge requires either a real checked export from
that existing native registry or a Pure Simple backend that creates and owns
the driver context/resources from initialization. The latter must replace the
real Engine2D and presenter resource paths together; locally constructed
identities and a second unconnected scheduler cannot supply it. Rust remains
outside the production fix. Async capability, live three-slot rendering,
source-image release, bounded aggregate scheduling, and C/Simple/Chrome
performance comparison remain unadmitted.

The pre-existing `dirty_rect_spec.spl` also requests bounded/coalesced and
display-clipped APIs absent from the current `dirty_rect.spl` implementation.
This checkpoint fix does not claim that independent bounded-damage gate passes;
it must be reconciled before the full async provider is admitted.
