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
