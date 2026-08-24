# SimpleOS scheduler address-space quiescence blocker

**Status: BLOCKED — unsafe prerequisite draft reverted.**

Safe ARM32 mapping destruction cannot be admitted from caller-supplied CPU
masks, CPU identifiers, or TTBR0 values. Those scalars are forgeable, and even
a genuine acknowledgement is insufficient if the scheduler can migrate the
task or reload its user root afterward. The rejected draft was removed rather
than expose a false destruction authority.

The required production owner must atomically:

1. fence dispatch and migration for the exact `(task_id, lifecycle_generation,
   mapping slot, mapping generation)`;
2. snapshot a scheduler-issued residency epoch and active CPU set;
3. send an owner-tracked IPI request to every captured CPU;
4. accept only completion receipts created by the architecture IPI handler
   after kernel-root restore, architecture-required barriers, TLB invalidation,
   and hardware root readback;
5. keep the dispatch fence held until a one-shot mapping destruction completes
   or its outcome is quarantined; and
6. recycle only positively destroyed receipt slots with a non-wrapping
   generation, while retaining failed/unknown mappings under a bounded
   operator-owned quarantine policy.

ARM32 needs an interrupt-side TTBR0 receipt provider tied to the scheduler
residency epoch. RV32/x86 need equivalent SATP/CR3 providers. None exists at the
current scheduler boundary, so integrating address-space destruction would be
unsafe. No production support or quiescence proof is claimed.
