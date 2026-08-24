# SimpleOS architecture switch quiescence lease blocker

## Blocker

The x86-32/x86-64, ARM32/ARM64, and RISC-V32/RISC-V64 switch adapters cannot
safely adopt canonical kernel-root registration or the same-address-space
no-write completion until one owner-issued CPU-pinning lease spans the complete
transaction:

1. capture the current CPU and exact prior interrupt state;
2. prevent migration and interrupts;
3. read or write CR3, TTBR0, or SATP and obtain exact readback;
4. complete the switch-owner transaction;
5. redeem or retain outgoing ownership;
6. restore the exact prior interrupt state on the same CPU.

The current CPU traits can disable and enable interrupts, but x86 and ARM do
not expose a common exact prior-state capture. The adapters also return before
completion/release. A caller-provided boolean or raw CPU ID is forgeable and
does not prove interval ownership, while blindly enabling interrupts would
violate callers that entered with interrupts already disabled.

## Required resolution

Add an opaque, nonce-validated, one-shot `ArchitectureCpuQuiescenceLeaseV1`
issued by architecture code from exact status-register readback. Bind it to CPU
ID and switch generation. Its owner must run adapter, completion, and outgoing
redemption within the lease and restore the captured state exactly once. Boot
kernel-root capture must use the same lease or a distinct non-migratable boot
lease. Only then may the six adapters call
`architecture_kernel_root_capture_v1` or
expose a same-address-space completion transition.

## 2026-08-24 static implementation review

Two implementation drafts were rejected and reverted without execution. The
review established additional prerequisites that must land atomically with the
lease rather than being inferred by an adapter:

1. RISC-V must expose a boot-captured, immutable hart identity. `tp` is task or
   per-CPU context and is not hardware identity proof across a migration.
2. Every architecture needs one topology-owned mapping from immutable hardware
   identity (full ARM affinity, x86 x2APIC identity, RISC-V hart identity) to
   the scheduler's bounded dense CPU ID. ARM Aff0 and the current x86/RV32
   single-CPU placeholders are insufficient.
3. The IRQ-off interval may not allocate or take a blocking thread-SFFI mutex.
   A fixed-capacity, freestanding, IRQ-safe per-CPU admission primitive must be
   available and linked for all six targets.
4. Lease authentication must bind CPU ID, switch generation, ticket nonce, and
   architecture kind. A terminal abort must consume any valid lease, cancel or
   quarantine the prepared switch, and restore exact prior IRQ state on the
   bound hardware CPU even when completion is rejected.
5. Exact restoration needs target evidence for x86 RFLAGS.IF, ARM64 DAIF,
   ARM32 CPSR I/F, and RISC-V sstatus.SIE in both initially-enabled and
   initially-disabled cases, plus replay, wrong-CPU, contention, cancellation,
   readback-mismatch, and exhaustion coverage.

No unsafe partial owner, runtime boundary, or adapter API is retained. Scheduler
wiring remains absent. No tests, builds, SPipe, benchmarks, optimizer, bootstrap,
or other runtime verification were run.
