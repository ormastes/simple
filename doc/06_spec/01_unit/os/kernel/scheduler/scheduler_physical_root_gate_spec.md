# Scheduler physical-root publication source contract

Source: `test/01_unit/os/kernel/scheduler/scheduler_physical_root_gate_spec.spl`.
Evidence class: **source-contract**. Authored manual; SPipe generation and SSpec
execution are **MissingEvidence**. No guest, mapping or successful spawn is
qualified by this manual.

## REQ-SCHED-ROOT-001 — image publication

1. Inspect the common production mapper admission gate. Verify roots `0` and
   `1` produce `-12` before direct-load or page-mapping backend access.
2. Inspect generic and slot-zero image creation. Verify every producer calls
   the mapper, rejects every nonzero status, attempts candidate retirement and
   returns failure before constructing a context. Inspect bytes preparation
   separately: it delegates a successful owned image to the common producer and
   returns preparation errors without constructing a TCB or using staged fields.
3. Inspect the ARM bootstrap producer before Ready publication. Verify its
   mapping failure returns before allocating identity or enqueueing the task.
4. Inspect authenticated adoption before selecting a task slot. Verify unavailable
   roots are rejected and every nonzero mapping result releases the candidate
   address space and quarantines adoption with `MapFailed`.
5. Inspect exec failure before releasing the current task address space. Verify
   failure retains the old task and unexpected positive status becomes `-12`.

## REQ-SCHED-ROOT-002 — fork publication

1. Inspect the parent-root rejection before the COW provider call. Verify a
   synthetic parent cannot reach cloning or task identity allocation.
2. Inspect the returned COW root before identity allocation. Verify failure and
   synthetic results cannot reach paired task/lifecycle reservation, Ready
   construction or VM registry publication. Store both coordinates from the
   accepted pair; the old ID-only allocator is not accepted.
3. Inspect the accepted-root flow into both publication records. Verify the
   child's returned root is retained consistently, with no parent-sentinel
   copying path.

## REQ-SPAWN-PREP-002 — operation-owned preparation

1. Inspect generic and bootstrap root construction. Require exact stack binding
   before physical allocation, then exact mapping and entry validation before
   paired task/lifecycle reservation. Mapping refusal must not consume an
   identity. If the allocator refuses the mapped candidate, attempt retirement
   through its real AddressSpace handle before returning failure;
   retain that lifecycle generation and explicit exec generation zero in the
   accepted TCB so unqualified generic exec cannot open snapshot admission.
2. Inspect a full generic task table: reject without replacing slot zero, even
   for a bootstrap caller.
3. Inspect the independent packet-admission owner: recognized packet calls
   still receive `-38` after shape validation. Internal image values grant no
   physical snapshot or publication authority.

<details>
<summary>Executable SSpec and evidence limits</summary>

The linked executable spec reads the production source and asserts admission
and publication ordering using the canonical matchers. A passing source check
does not execute these owners. The test plan lists required physical fault
injection and the existing base constructor mismatch that prevents assuming
compiled readiness from this repair.

The non-x86 shallow COW provider lacks an owned rollback receipt. A valid raw
COW root followed by identity-allocation refusal therefore has no safe subtree
destruction path; its shared parent tables must not be freed. This is a tracked
MissingEvidence prerequisite in
`doc/08_tracking/bug/scheduler_cow_identity_refusal_rollback.md`, not a completed
rollback claim. The x86 COW provider remains fail-closed before allocation.

</details>
