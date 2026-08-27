# RISC-V 64 QEMU Release Lineage and Nonce Gap

**Date:** 2026-08-11  
**Status:** OPEN  
**Acceptance criteria:** AC-7, AC-14

## Proven diagnostic behavior

Descriptor-identical Linux QEMU boots the canonical RV64 acceptance kernel and
shared-storage FAT32 image. The guest enumerates ten real `/SYS/APPS` entries,
loads an executable RV64 ELF from FAT32, executes its instructions, emits target
UART stdout, returns zero, and reaches `TEST PASSED`.

Evidence:

```text
/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/riscv64/20260811T054000Z/
```

## Remaining release blockers

1. Cross-target compilation used the Rust bootstrap seed because the deployed
   pure-Simple compiler does not currently provide this target path.
2. The guest markers are not yet correlated with a per-run nonce supplied by
   the runner, so the strict receipt classifier cannot accept them.

The behavior is real but remains diagnostic until both facts are corrected and
the canonical system spec is run once through the deployed pure-Simple CLI.

## Ownership

- Owner: RISC-V64 SimpleOS execution lane
- Merge owner: SOSIX/QEMU integration lane
- Final reviewer: independent normal/highest-capability reviewer
