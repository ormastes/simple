# Vulkan no-wait submission blocks the next compute command

**Status:** OPEN
**Found:** 2026-09-09
**Component:** Vulkan runtime compute ownership

## Defect

`rt_vulkan_submit_no_wait` returns after queue acceptance and retains the
command, fence, pipeline, descriptor set, and buffers in
`VulkanState.quarantined_compute` with a caller-visible `wait_handle`. However,
`rt_vulkan_begin_compute` refuses whenever that vector is non-empty, without
distinguishing a waitable pending submission from the zero-handle
completion-unknown quarantine.

Consequently, a pure-Simple resident renderer cannot enqueue a bounded ring of
recyclable frame slots: the first no-wait submit succeeds and a later
`begin_compute` fails. Several commands can be pre-recorded before the first
submit and then submitted as a finite batch, because `submit_no_wait` does not
apply the quarantine gate. That is not a sustained ring: waiting and destroying
a fence does not remove its native quarantine entry;
`rt_vulkan_destroy_fence` only revokes its public handle. A device-idle reap is
then required before a replacement command can begin, which defeats continued
CPU/GPU overlap.

The representation also conflates states: completion-unknown submissions are
created with `wait_handle = 0`, while
`release_quarantined_wait_handle` assigns the same zero value when a caller
revokes an ordinary waitable handle. A future ring must add an explicit state
tag and must not orphan a pending submission by destroying its only token.

## Current honest behavior

`vulkan_resident_2d.spl` continues to use
`vulkan_sffi_submit_and_wait_fence`, increments
`blocking_queue_submit_calls` for every attempt, and leaves
`device_scene_nonblocking_submits` at zero. It does not claim asynchronous
submission.

## Required runtime fix and evidence

The runtime owner must distinguish waitable pending work from genuinely unknown
completion, allow new command allocation while only waitable submissions are
pending, and release a signaled quarantined command plus all retained owners
when its fence is retired. Descriptor updates must remain forbidden while a
submission using that descriptor may still execute.

Acceptance requires a Vulkan device test that enqueues at least three commands
before any host wait, proves all three caller fence handles remain resolvable,
retires one, recycles its generation, and submits a fourth without device idle,
then verifies no command/fence/resource owner remains. A ring-full case must
apply bounded backpressure. A stale token, timeout, or unknown-completion
negative control must block unsafe reuse and preserve every resource until
completion proof or explicit recovery.

This is a Rust runtime change and was not made by the pure-Simple optimization
review.

## Pure-Simple ownership review (2026-09-09)

The available Simple sequence was traced through
`src/lib/gc_async_mut/gpu_lane/vulkan_lane_session.spl` and
`src/lib/nogc_sync_mut/gpu/engine2d/sffi_vulkan.spl`. A zero-timeout
`vulkan_sffi_wait_fence` is only an observation. A subsequent
`vulkan_sffi_destroy_fence` revokes the public handle but leaves the runtime
quarantine entry alive. `vulkan_sffi_reap_dependency_quarantine` can make the
next `begin_compute` succeed only by proving device idle, which serializes the
queue and is not an async ring.

The Simple-side arrays in `VulkanLaneSession` and the engine backend are not
authority: they contain copied integer handles and cannot inspect
`VulkanState.quarantined_compute` or release `ComputeCommandOwners`. Therefore
no safe Simple-only ring implementation exists against the current API. No
Rust/C/device change was made in this review.

Requirement options and the selected-capability design are recorded in:

- `doc/02_requirements/feature/vulkan_async_compute_submission_ring.md`
- `doc/02_requirements/nfr/vulkan_async_compute_submission_ring.md`
- `doc/05_design/runtime/vulkan_async_compute_submission_ring.md`
- `doc/03_plan/sys_test/vulkan_async_compute_submission_ring.md`
