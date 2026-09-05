# SimpleOS CPU interrupt-quiescence architecture adapter blocker

Date: 2026-08-24

Status: BLOCKED — production adapter implementation would currently fabricate
CPU pinning and architectural readback evidence.

## Requested production transaction

For x86-32/x86-64, ARM32/ARM64, and RV32/RV64, one same-CPU architecture
boundary must:

1. read the exact hardware identity (APIC/x2APIC ID, canonical MPIDR, or hart ID),
   derive its logical CPU through the sealed snapshot, and obtain an owner-issued
   pin without accepting a caller-supplied logical CPU as authority;
2. re-read and validate the same hardware identity after pin acquisition;
3. use a trusted ordered save-and-mask boundary with no scheduler escape between
   capture and masking;
4. reserve and publish `CpuInterruptQuiescenceLeaseV1` with that observed state;
5. run the existing target-specific address-space switch adapter;
6. re-read identity and disabled state, complete and redeem the lease;
7. restore the exact prior mask state, re-read it, finish the restore receipt;
8. release the CPU pin only after the restore receipt is accepted. If failure
   occurs after reservation/publication, retain both the quiescence slot and pin
   until an explicit quarantine/recovery owner accepts their disposition.

No caller-provided CPU scalar or interrupt boolean may substitute for hardware
evidence. A failure after lease publication must retain/quarantine ownership;
it may not recycle a possibly live generation.

## Current blockers

### No effective CPU-pin owner

`src/os/kernel/smp/percpu.spl` contains `percpu_preempt_disable` and
`percpu_preempt_enable`, but no production scheduler path calls
`percpu_preempt_enabled`. The counter is a copyable scalar in a mutable table,
has no owner-issued one-shot lease, can overflow, and is not enforced by task
selection or interrupt-return dispatch. It therefore cannot prove that the
restore readback still executes on the CPU that reserved the quiescence lease.

This matters most when the prior state was enabled: restoring interrupts can
admit a scheduling interrupt before a separately implemented CPU-identity
readback. A real pin must remain effective across that window.

### Hardware identities are not production-exact on all targets

- `src/os/kernel/arch/x86_64/cpu.spl` and
  `src/os/kernel/arch/x86_32/cpu.spl` return constant CPU ID `0`.
- `src/os/kernel/arch/riscv32/cpu.spl` also returns constant hart ID `0`.
- ARM `cpu_id` helpers retain only MPIDR Aff0, while the sealed topology owner
  canonicalizes Aff3:Aff2:Aff1:Aff0.
- RV64 uses `tp`; that is usable only while the boot contract continues to
  reserve `tp` as the stable hart identity and no per-CPU-base migration
  repurposes it.

The x86 path additionally needs an x2APIC-capable identity read (for example,
CPUID topology leaf identity with a defined fallback), not the existing
single-CPU placeholder.

### Exact interrupt save/readback/restore is absent

The existing CPU leaves expose disable/enable operations, not an exact saved
interrupt-mask field plus readback. The ordered boundary need not claim one
architectural instruction: x86 and ARM naturally require ordered instruction
sequences, while RISC-V can use a CSR read/modify/write primitive.

- x86 needs the RFLAGS.IF field, CLI, disabled readback, and conditional IF restore;
- ARM64 needs DAIF save/readback and restoration of the prior mask bits;
- ARM32 needs CPSR I/F save/readback and restoration of the prior mask bits;
- RISC-V needs sstatus.SIE save/clear/readback and conditional restoration.

The bool stored by `CpuInterruptQuiescenceOwnerV1` can validate the primary IRQ
enable state, but a target adapter must retain and restore the relevant exact
mask material locally: x86 IF, RISC-V SIE, and the ARM DAIF/CPSR I/F field. It
does not need to retain unrelated RFLAGS, sstatus, DAIF, or CPSR material.
Calling the current address-space switch
adapters is insufficient: they only disable and intentionally leave interrupts
disabled; they do not save or restore prior state.

### No boot-published topology or quiescence owner

Both `CpuTopologyIdentityOwnerV1` and `CpuInterruptQuiescenceOwnerV1` are
referenced only by static specifications. No boot owner registers and seals the
canonical topology, constructs the quiescence owner from its snapshot, or
publishes a single canonical architecture port. Adding leaf functions without
those owners would create more unreachable source, not production integration.

The six existing address-space completion adapter leaves are likewise
source-only and have no production callers. There is therefore no current
canonical dispatch to replace; the future dispatch must expose only the
quiescence-wrapped entry points while retaining the raw target leaves as
package-private implementation details.

## Required coherent fix

Land these pieces as one reviewed ownership change:

1. an owner-issued, non-wrapping CPU-pin lease enforced by scheduler selection
   and interrupt-return dispatch;
2. exact target hardware identity primitives for all six targets;
3. exact target save-mask/readback/restore primitives, with full ARM mask state
   retained by the adapter;
4. one boot owner which registers, seals, and publishes
   `CpuTopologyIdentityOwnerV1`, then builds one
   `CpuInterruptQuiescenceOwnerV1` from that snapshot and publishes it through a
   target-selected architecture port;
5. wrappers around all six `address_space_switch_completion_adapter_v1` leaves
   which perform the full transaction above; the future canonical production
   dispatch must expose only these wrappers and keep the raw leaves
   package-private;
6. failure-injection coverage for identity mismatch, pin replay/overflow,
   already-disabled entry, enabled restore, partial ARM masks, switch rejection,
   restore mismatch, stale lease/permit replay, and post-publication failure
   that retains both the pin and slot until explicit recovery.

Until all six prerequisites are present, adapters must remain absent. A wrapper
that accepts a CPU ID/IRQ boolean, uses the current constant IDs, or calls the
unenforced preemption counter would be unsafe and must not be described as
production support.

## Verification status

Unverified by explicit user instruction: no tests, builds, SPipe, benchmarks,
optimizer, bootstrap, or runtime verification were run while recording this
blocker.
