# Vulkan Async Compute Submission Ring — Design and Acceptance Plan

**Status:** selected B/N2 design; no runtime implementation is authorized by
this document until the acceptance gates pass.

**Selected contract:** one runtime-owned session per device generation, with a
construction-time capacity of 3–16 and at most one configured bounded wait on a
ring-full event. N1 remains a diagnostic fixed-three-slot comparison row.

## Current ownership classification

| State or operation | Canonical owner | Boundary classification | Safe Simple action |
|---|---|---|---|
| `VulkanState.quarantined_compute` | Rust Vulkan runtime | runtime-owned lease table | none; opaque |
| command buffer and `ComputeCommandOwners` | runtime until fence retirement | owned move into submission lease | record only a copied receipt |
| caller fence integer | Simple caller token | handle/lease name, not ownership | wait or request retirement |
| descriptor/buffer resources | runtime + command lease | retained owners scoped to fence | do not free before retirement |
| `wait_fence(..., 0)` | runtime fence observation | observation, not retirement | use as poll only |
| `destroy_fence` | runtime handle revocation | lease-name release only | cannot unlock command gate |
| `wait_idle` + quarantine reap | runtime/device owner | global quiescence proof | recovery/teardown only |

The GPU queue is a separate execution domain. A numeric handle copied into
Simple is not a transfer of command/resource ownership. A child or frame owner
may publish only a fence/slot receipt; the runtime remains authoritative for
retaining and dropping device objects.

Public resource-handle release and physical resource destruction are distinct.
The current Rust maps may revoke a buffer, pipeline, or descriptor handle while
`Arc` owners retained by a recorded/submitted command keep the physical object
alive. A selected design may instead reject early release, but it must define
one policy consistently: it may never reuse the public identity for a new
object or physically destroy the old object before every referencing submission
retires. Shader modules are pipeline-creation inputs and need not remain live
after pipeline creation; they are not members of `ComputeCommandOwners`.

## Why Simple-only sequencing is insufficient

The safe sequence available today is:

```text
begin -> record -> submit_no_wait -> wait_fence -> destroy_fence
                                              -> wait_idle/reap -> begin next
```

The last step is mandatory because `begin_compute` rejects every nonempty
`quarantined_compute`, while `destroy_fence` only clears `wait_handle`. Calling
`begin_compute` after a successful fence wait and handle destroy therefore
fails closed; calling it after only `wait_fence` also fails. Calling
`reap_dependency_quarantine` proves device idle and works, but removes all
asynchronous overlap. A local Simple ring cannot change this private runtime
gate.

There is one limited exception that is not a ring: callers can invoke
`begin_compute` several times before the first `submit_no_wait`, then submit
those pre-recorded commands as one finite batch. `submit_no_wait` itself does
not reject because an earlier submission is quarantined. Once submission has
started, however, no replacement command can be recorded and no completed slot
can be reaped without device idle. Acceptance must therefore include recycling
a slot and submitting command N+1, not merely submitting a pre-recorded batch.

## Candidate runtime interface shape (after A/B selection)

The implementation must expose one of the selected option's exact contracts,
with the following invariants common to both:

1. Waitable pending entries are distinguishable from invalid/stale tokens,
   caller-revoked tokens, and completion-unknown entries through an explicit
   state tag. Current code writes `wait_handle = 0` for both an originally
   unknown submission and ordinary handle revocation, so handle value alone is
   not evidence. Pending, invalid, and device-loss results may not share one
   return code.
2. Retirement identifies one exact device/session/slot generation and first
   proves its fence signaled with a zero-timeout status query. No stale token
   may address a reused slot.
3. Retirement frees the command buffer and drops every retained owner exactly
   once, then publishes a terminal retirement receipt. Repeating an owner-side
   close is idempotent; repeating a consumed raw token is rejected as stale and
   must not free anything again.
4. New recording is allowed only while no unknown-completion entry exists and
   the selected bounded capacity has a free slot. Capacity counts recording,
   submitted, and completed-awaiting-retirement states. Option A enforces a
   runtime-wide fixed bound of three; Option B enforces the chosen session
   bound (3–16). Submit transitions a reserved recording slot and cannot grow
   the owner table.
5. Descriptor mutation is rejected while any live command/submission retains
   that descriptor. Public resource release either rejects or revokes only the
   token while physical `Arc` ownership remains live; the chosen policy must be
   consistent and tested for buffers, descriptors, pipelines, and shaders.
6. Cancellation is admission closure, not GPU preemption. Submit failure before
   queue acceptance can release the unsubmitted command. Timeout retains the
   live lease. Device loss or any ambiguous submit/status result fail-stops the
   ring and retains owners until explicit recovery or device teardown.
7. Shutdown closes admission first, drains proven completions, then may use one
   explicit device-idle recovery. The normal submit/poll/retire path may never
   call `wait_idle`, directly or through a helper.
8. Checked handle/session/slot generation allocation fails closed before zero,
   negative values, collision, or wraparound. Teardown invalidates every token
   before storage can be reused.
9. Counters distinguish attempted/accepted/rejected submits, polls and their
   outcomes, bounded CPU waits and duration, backpressure, retirements,
   cancellation, maximum in-flight slots, retained/released bytes,
   completion-unknown transitions, and device-idle recoveries.
10. Host timestamps use a monotonic clock. Optional Vulkan timestamp-query
    samples carry an availability bit and are reported separately from host
    submission/retirement latency.
11. A bounded host fence wait may not hold the global `VulkanState` registry
    mutex. Option B must pin a generation-bound per-slot `Arc` lease, release
    the registry lock, wait through that lease, then reacquire and revalidate
    the generation before retirement. Cancellation cannot destroy the pinned
    lease. Queue locking covers queue submission only, never host waiting.
12. `destroy_fence` cannot revoke the only name of a live submitted entry. It
    either rejects without mutation or delegates to signaled-only exact
    retirement; pending and ambiguous entries retain a resolvable owner token.
13. Option B v1 admits one compute-ring session per device generation. The
    session holds the direct-compute admission lease; legacy global compute
    begin/submit and device shutdown reject while it is live. Supporting more
    sessions later requires a device-owner aggregate capacity, not independent
    per-session vectors that can grow without bound.

Option A's candidate retirement result vocabulary is:

- `1`: retired.
- `0`: valid and pending.
- `-1`: invalid, stale, or wrong-device token.
- `-2`: completion unknown or device lost.

Successful retirement consumes the live token; the
Simple slot records the returned terminal receipt. Option B should expose the
same distinctions through generation-bound session/slot operations rather than
a naked global fence handle.

The common slot lifecycle is:

```text
Free(g) -> Recording(g) -> Submitted(g) -> CompletedAwaitingRetirement(g)
        -> Free(g+1)
```

Failure before queue acceptance returns the slot to `Free(g+1)`. Ambiguous
acceptance or status moves it to `CompletionUnknown(g)`, closes session
admission, and forbids reuse until recovery or device teardown proves ownership
resolved.

## Simple-side owner-result ring

After runtime capability admission, the Simple renderer may own a fixed array
of N slot receipts (`fence`, `frame_generation`, `resource_generation`, byte
counts, and state). It is a bounded owner-result structure, not a second
resource owner. The renderer submits immutable frame snapshots and assigns a
strictly increasing sequence. It polls the oldest unpublished sequence first.
Physical slots may retire in proven completion order, but frame-visible results
are buffered and published only as the contiguous sequence prefix. A slot may
be reused only after its runtime retirement receipt and a new slot generation.
On ring-full, N1 polls once and returns `would-block`; N2 may additionally make
one bounded wait. Neither policy busy-spins or grows capacity. On unknown
completion the owner closes admission, preserves every slot receipt, and
requests explicit recovery.

## Acceptance plan

1. Device-free contract: invalid command/fence/slot inputs return explicit
   failure; no fabricated fence or success counter is allowed.
2. Live-device positive: record and submit at least three commands before any
   host wait; all three caller handles/slot receipts resolve; poll/retire each;
   recycle one slot and submit command four without device idle; verify no
   command, fence, device, pipeline, descriptor set/pool/layout, or buffer owner
   remains.
3. Interleaving: fill the ring, prove the full-ring backpressure result, poll
   the oldest with zero timeout, and submit another only after exact retirement.
   Force out-of-order completion where supported and verify physical retirement
   never changes deterministic frame receipt order.
4. Negative timeout: a pending fence returns pending without freeing owners;
   invalid/stale and completion-unknown states return different results. A
   caller handle-destroy attempt cannot turn pending work into an unnamed
   entry. Completion-unknown blocks recording and preserves every owner until
   device-idle recovery or device teardown.
5. Resource safety: descriptor update fails while referenced by any live slot.
   For buffer/descriptor/pipeline release, verify the selected
   reject-or-token-revoke policy and prove the physical object stays retained
   until exact retirement. Verify shader release after pipeline creation remains
   safe and does not fabricate slot residency. Attempt stale-token use after
   slot reuse.
6. Teardown: cancellation closes admission and drains accepted work without
   claiming GPU preemption. Repeated owner close is idempotent. Any explicit
   teardown/recovery device-idle call increments its counter; that counter stays
   zero on the normal path.
7. Performance evidence: compare C Vulkan and Simple on the same viewport,
   primitive count, warmup/sample count, readback mode, device identity, p50,
   p95, CPU wait count/duration, maximum in-flight slots, backpressure,
   accepted/rejected submits, retired slots, retained bytes, and RSS. Record
   monotonic host timings and optional available GPU timestamps separately.
   Report blocking and finite pre-recorded-batch baselines separately from a
   recyclable async-ring row.
8. Contention: during an N2 bounded wait, a second thread can query counters or
   poll another slot; prove no global registry mutex is held for the wait.

The executable spec belongs under
`test/02_integration/gpu/vulkan_async_compute_submission_ring_spec.spl` after
selection and runtime capability implementation. Generated/manual evidence
must be placed under `doc/06_spec`, never as an executable `.spl` file.

## Astra implementation review, 2026-09-09

The selected B/N2 candidate now has explicit configurable pressure waiting,
generation-safe fence pinning, bounded receipt publication, scalar telemetry,
and explicit idle recovery. Provider ABI v1 keeps async as an optional complete
extension. The detailed exported ABI, telemetry word map, and emergency device
quarantine semantics are in
`doc/07_guide/platform/ffi/vulkan_async_session.md`.

Failed idle recovery never authorizes destruction. Emergency abandonment
detaches and retains the entire device generation; it returns a distinct
quarantined result and requires process restart before reinitialization.
It is not physical-release or automatic device-recreation evidence.

The dependency-free production protocol tests and injected-provider tests
exercise slot capacity, recycling, failure retention/release, cancellation,
snapshot integrity and two-thread wait/registry interleaving. The latter compile
the actual owner modules with a substituted low-level device/fence boundary.
Neither replaces the live-device, descriptor/pipeline-owner, admitted Simple
caller/link, lifecycle integration or matched-performance gates above.
