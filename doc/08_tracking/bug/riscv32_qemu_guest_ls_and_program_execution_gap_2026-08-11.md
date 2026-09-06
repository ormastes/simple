# RISC-V 32 QEMU Guest `ls` and Program Execution Gap

**Date:** 2026-08-11  
**Status:** IMPLEMENTED DIAGNOSTICALLY — release lineage/correlation open  
**Acceptance criteria:** AC-7, AC-14

## Reproduction

The canonical RISC-V 32 kernel and newly generated FAT32 image boot successfully
under the descriptor-identical QEMU command. Retained evidence:

```text
/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/riscv32/20260811T050100Z/
```

The first serial transcript proves boot, FAT32 mount, SMF discovery, and ELF
loading. A rebuilt diagnostic kernel then performed real FAT32 enumeration and
printed ten `/SYS/APPS` entries from disk. That transcript is retained at:

```text
/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/riscv32/20260811T051200Z/serial.log
```

The next rebuilt image contains a real position-independent RV32 ELF loaded
from FAT32. Its instructions write `hello from rv32 filesystem program` to the
target UART and return zero; the kernel observes that return. Retained evidence:

```text
/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/riscv32/20260811T052000Z/
```

## Root cause

`examples/09_embedded/simple_os/arch/riscv32/smoke_entry.spl` invokes probe and
load helpers only. In
`examples/09_embedded/simple_os/arch/riscv32/boot/baremetal_stubs.c`,
`riscv_load_elf_process` validates and copies ELF segments into an arena, records
an entry address and PID, then returns. It neither transfers control to the
loaded entry. The listing half was fixed by
`rt_riscv32_fat32_list_sys_apps`, which walks the actual FAT cluster chain and
emits each non-LFN directory entry read from `/SYS/APPS`.

This was fixed by recording the mapped physical entry, issuing `fence.i`, and
calling the loaded entry. The generated payload is executable RV32 code rather
than the earlier marker-only ELF fixture. `SMF_CLI_LAUNCH_OK` alone still means
load/registration; the independent `FS_PROGRAM_*` sequence and UART stdout are
the execution proof.

## Unblock condition

1. Add run-nonce correlation to the real listing markers at the runner/guest
   boundary.
2. Rebuild the kernel with a deployed pure-Simple compiler rather than the
   cross-target bootstrap seed.
3. Run the canonical system spec once and classify the retained transcript with
   `sosix_qemu_guest_serial_status`.

Do not replace these operations with fixed marker strings.

## Ownership

- Owner: RISC-V 32 SimpleOS execution lane
- Merge owner: SOSIX/QEMU integration lane
- Final reviewer: independent normal/highest-capability reviewer
