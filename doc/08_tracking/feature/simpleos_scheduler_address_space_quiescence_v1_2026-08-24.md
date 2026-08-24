# SimpleOS scheduler address-space quiescence blocker

**Status: BLOCKED — bounded IRQ lease prerequisite landed locally; production
architecture adapters and scheduler integration remain absent.**

The second draft added bounded epoch/nonce rows, a mutex, one-shot snapshots,
and canonical scheduler admission, but it still cleared the outgoing CPU lease
before the architecture switch path had restored and confirmed another root.
A concurrent fence could therefore observe an empty scheduler set while the
CPU still executed the old task or retained its CR3/TTBR/SATP root. The draft
was reverted; no false quiescence authority remains.

Safe ARM32 mapping destruction cannot be admitted from caller-supplied CPU
masks, CPU identifiers, or TTBR0 values. Those scalars are forgeable, and even
a genuine acknowledgement is insufficient if the scheduler can migrate the
task or reload its user root afterward. The rejected draft was removed rather
than expose a false destruction authority.

The required production owner must atomically:

1. reserve an incoming dispatch while retaining the outgoing task's active CPU
   lease and bind the fence to exact task/mapping generations;
2. perform the architecture root switch and required barriers, then accept a
   non-forgeable interrupt/context-switch completion before releasing the
   outgoing lease;
3. snapshot a scheduler-issued residency epoch and private active CPU set;
4. send an owner-tracked IPI request to every captured CPU;
5. accept only completion receipts created by the architecture IPI handler
   after kernel-root restore, architecture-required barriers, TLB invalidation,
   and hardware root readback;
6. keep the dispatch fence held until a one-shot mapping destruction completes
   or its outcome is quarantined; and
7. recycle only positively destroyed receipt slots with a non-wrapping
   generation, while retaining failed/unknown mappings under a bounded
   operator-owned quarantine policy.

ARM32 needs an interrupt-side TTBR0 receipt provider tied to the scheduler
residency epoch. RV32/x86 need equivalent SATP/CR3 providers. None exists at the
current scheduler boundary, so integrating address-space destruction would be
unsafe. No production support or quiescence proof is claimed.

`cpu_interrupt_quiescence_lease_v1.spl` now supplies the safe owner-side
state machine needed by those providers: one boot-sized atomic slot per sealed
logical CPU, exact architecture/hardware identity and generation binding,
one-shot save-disable/completion/restore transitions, prior-state restoration,
and terminal quarantine on mismatch or generation exhaustion. Its IRQ-side
transitions do not allocate, block, or take a mutex. This is not yet a hardware
quiescence proof: the x86/ARM/RISC-V privileged adapters which atomically read
the prior interrupt bit, disable, re-read identity/state, and restore are still
required, and the scheduler has not been wired to the capsule.

The owner also needs an explicit policy for mutex-unlock failure after a
committed mutation (terminal poison/quarantine or a proven infallible unlock),
and task liveness/removal must share the same serialized owner transaction.
