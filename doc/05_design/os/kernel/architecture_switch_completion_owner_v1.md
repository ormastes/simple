# Architecture switch completion owner v1

## Scope

This owner closes the lifecycle gap between a scheduler selecting an incoming
address space and the mapping owner being allowed to release the outgoing
residency reference. It is bounded to 64 CPUs and one in-flight switch per CPU.

It does **not** destroy mappings, publish task readiness, enter user mode, or
replace the architecture CPU path. Those actions remain deliberately absent.

## Ownership protocol

1. `architecture_switch_register_current_v1` seeds the current, live mapping
   identity for a CPU exactly once.
2. `architecture_switch_prepare_v1` checks that the caller's outgoing identity
   is the current identity, retains it in the owner, and reserves the incoming
   identity under a fresh generation and nonce.
3. The privileged architecture path consumes pre-write cancellation authority,
   enters `Installing`, writes CR3, TTBR0, or SATP, executes its
   required TLB/barrier sequence, reads the register back, and creates the
   matching package-private architecture receipt.
4. `architecture_switch_complete_v1` consumes matching coordinates and exact
   readback evidence. `architecture_switch_redeem_outgoing_release_v1` then
   returns the outgoing coordinate exactly once; replays fail closed.

A failed or malformed post-write receipt quarantines the per-CPU slot while retaining both mapping
coordinates. It cannot authorize rollback because hardware may already be
executing with an unknown root. Cancellation is valid only before the write.

## Architecture adapters

- x86-32/x86-64 compare the page-aligned CR3 address while allowing defined
  low control/PCID bits.
- ARM32 compares the 16-KiB-aligned TTBR0 root; ARM64 compares the 4-KiB root
  while excluding ASID/control bits.
- RV32 encodes Sv32 SATP; RV64 encodes Sv48 SATP, both with ASID zero.

The architecture leaves `address_space_switch_completion_adapter_v1.spl`
check the executing CPU identity, disable interrupts, recheck identity, then
perform the privileged write, required TLB/barrier operation, readback, and
receipt construction without exposing an intermediate successful receipt.
They intentionally leave interrupts disabled for the surrounding scheduler
restore/entry path; they are not general application-callable switch helpers.
Scheduler integration must call the selected target leaf, immediately feed its
result to the owner, and pass the one-shot-issued release coordinate to a mapping
owner that consumes the switch generation idempotently. The returned value is
copyable, so this component claims exactly-once issuance, not exactly-once
downstream destruction. This change deliberately does
not replace the current context-switch call site.

## Canonical scheduler wiring blocker

Static integration review on 2026-08-24 found that wiring the owner directly
into `Scheduler.schedule_on_cpu` would be unsafe. That method owns selection and
task-state publication only: it returns a portable `TaskContext` and does not
own the privileged CR3, TTBR0, or SATP write. The live architecture user-entry
bridges currently perform those writes later, through separate target-specific
paths. Preparing a switch in `schedule_on_cpu` would therefore retain an
outgoing residency with no guaranteed same-CPU completion, cancellation, or
readback call. It would also run after ready-queue, task-state, `current`,
`current_by_cpu`, and replay-hook publication, even though the method has no
failure or receipt return channel through which a rejected or quarantined
hardware switch could roll that publication back.

The initial kernel-to-user transition is also not representable by this v1
owner. `architecture_switch_register_current_v1` requires a nonzero, page-
aligned residency identity, while the scheduler and address-space bridge use
root `0` as the kernel identity sentinel. Substituting a fabricated nonzero
mapping identity would turn the safety check into false evidence.

Finally, a `TaskControlBlock` currently exposes a physical root and task
lifecycle generation, but no canonical cross-architecture mapping identity and
mapping generation for every task. Those values cannot be synthesized from the
PID, root, isolation profile, or lifecycle generation: they belong to the
architecture mapping owners. The one-shot outgoing release receipt likewise
has no canonical consumer that can decrement residency without destroying or
changing readiness.

Scheduling another task that shares the already-installed address space is a
normal case, but `architecture_switch_prepare_v1` deliberately rejects equal
residency identities. No authoritative no-op receipt exists yet. In addition,
the trusted adapters disable interrupts before the privileged write and leave
them disabled for a surrounding restore/entry path; the scheduler does not yet
define which dispatch boundary owns restoration for voluntary versus interrupt
entry. Calling these adapters from selection code would therefore change
interrupt state without a proved terminal handoff. Leaving the older
`address_space_switch` and per-architecture user-entry writers reachable would
also create unowned or duplicate hardware switches.

Safe wiring therefore requires all of the following in one ownership-coherent
change:

1. represent the kernel address space as a real, owner-issued residency identity
   (or add an explicit kernel-sentinel transition to the completion protocol);
2. expose owner-issued mapping identity/generation queries for all six target
   adapters without copying destruction authority into the TCB;
3. move prepare, privileged adapter dispatch, completion, and outgoing-release
   redemption into one same-CPU architecture dispatch boundary, with an
   explicit same-residency no-op receipt and interrupt restoration owner;
4. add an idempotent mapping-owner residency-release ingress that consumes the
   exact switch generation without freeing mappings or publishing readiness;
5. make scheduler selection transactional so failed pre-write preparation can
   cancel without publishing selection, while post-write indeterminacy can
   quarantine the dispatch rather than rolling hardware state back; and
6. route every live context/user-entry writer through the same architecture-
   neutral port before removing the legacy direct-write paths.

Until those prerequisites exist, the current owner and adapters remain safe
primitives, but claiming canonical scheduler wiring would be incorrect.

## Performance and safety

Each prepare/complete operation uses O(1) indexed per-CPU state. The backing
array grows at most once per admitted CPU and is capped at 64 entries. No byte
buffers, page-table copies, root scans, or mapping destruction occur on the
context-switch hot path. A checked mutex serializes mutation until scheduler
code supplies a stronger per-CPU critical-section owner.

## Unverified handoff

The source and focused specifications are authored but not executed in this
lane by instruction. Live integration still requires scheduler consumption of
the target adapter and its release receipt.
