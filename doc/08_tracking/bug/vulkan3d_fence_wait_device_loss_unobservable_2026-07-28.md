# Vulkan3D fence/wait-idle device loss is not observable to Simple

- **ID:** `vulkan3d_fence_wait_device_loss_unobservable_2026-07-28`
- **Status:** SOURCE FIXED — RUNTIME UNVERIFIED
- **Severity:** high (blocks complete NFR-007 device-loss evidence)
- **Owner:** `stage3_hir_lifetime` (source); `/root` (final review)

## Source-fixed status

The former defect was that fence-wait and wait-idle failures returned false
without updating the canonical Vulkan last-error owner. Current source retains
both failures there and `VulkanRenderBackend3D` classifies them through its
existing `vulkan_last_error()` path. This is source-fixed but has not executed
through an admitted current pure-Simple CLI/core-C runtime.

## Implemented source repair

Failed graphics fence wait and wait-idle now retain the exact Vulkan error in
the existing runtime last-error owner before returning. The pure-Simple backend
classifies exact `DEVICE_LOST`/`device lost` text as `device-lost`, keeps the
observation sticky through CPU fallback, and exposes it only through the
font-owner facade. No second error channel or synthetic receipt was added.

## Verification

- Submit, fence-wait, and wait-idle device loss all produce the same owner-backed
  `FontOwnerFaultReceipt.DeviceLoss` scalar.
- Non-device-loss wait failures remain `Unknown` and cannot promote NFR-007.
- Existing cleanup/quarantine and unchanged batch identity remain intact.

Until this source repair executes through an admitted pure-Simple CLI and real
Vulkan lane, NFR-007 remains blocked rather than treating static coverage as
complete device-loss evidence.
