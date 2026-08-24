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

No unsafe partial adapter wiring is retained.
