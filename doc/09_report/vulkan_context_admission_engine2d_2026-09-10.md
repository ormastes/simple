# Pure Simple Engine2D Vulkan context admission — 2026-09-10

Status: **WARN — honest production admission gate; async is not enabled.**

The package `src/lib/gc_async_mut/gpu/engine2d/vulkan_context_admission.spl`
now consumes the existing live `VulkanBackend` owner and its retained
`VulkanSession`. It does not accept caller-supplied device/session identities,
create a second session, invoke `wait_idle`, or use a readback as a completion
receipt. Unavailable results zero all identity fields even if a caller
populated positive backend handles.

The production unavailable path returns before DrawIR serialization, avoiding
a second composition traversal on every synchronous frame. The separate
candidate helper uses the existing bounded canonical codec and rejects
malformed compositions, but its packet grants no provider authority.

`Engine2D.vulkan_async_admission()` is the production consumer boundary. The
window-present DrawIR route queries it and records admission status, reason,
packet checksum, and `async_claim` in `Engine2dDrawIrAdvResult`. While the
provider cannot prove exact context membership, the route remains on the
existing synchronous owner; no-backend and unsupported-binding states report
their exact unavailable reason and retain a zero packet checksum.

The gate preserves the selected 3–16 capacity policy and rejects malformed
DrawIR/capacity before any provider work. It also rejects an active legacy
recording or unknown completion state. It does **not** claim bounded async
pressure, exact slot generations, compute receipts, presenter release, or
hardware performance; those require a canonical provider context-binding and
presenter-release ABI plus admitted runtime evidence.

Evidence:

- `test/01_unit/lib/gpu/engine2d/vulkan_context_admission_spec.spl` covers
  device-free capacity rejection, valid and malformed canonical packet
  encoding, caller-populated handle rejection, the zero-serialization
  unavailable result, synchronous rendering preservation, and explicit
  absence of async authority.
- `git diff --check` passed after the implementation.
- Sol cycle-1 review removed the original unconditional production packet
  serialization and zeroed locally populated handles in unavailable results.
- Working and staged direct-environment runtime guards passed.
- The one requested Simple check attempt could not execute because no admitted
  cached self-hosted check worker artifact is available; the seed printed its
  existing bootstrap-only warning. No Rust/C implementation was added.
