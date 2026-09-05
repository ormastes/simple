# SOSIX/QEMU Matrix: Current-Host Media and Self-Hosted Runner Blockers

**Date:** 2026-08-11  
**Status:** OPEN  
**Acceptance criteria:** AC-3 through AC-8, AC-10 through AC-14

## Observed state

The Linux host QEMU preflight passes for x86_64/i386, ARM32, ARM64, RISC-V32, and RISC-V64 binaries and reports usable KVM. Shared storage is `/mnt/data/.simple/qemu`.

No guest row currently has both canonical kernel and filesystem media:

| Guest | Kernel | Image |
|---|---|---|
| x86_32 | present via shared-storage symlink (`build/os/simpleos_x86_32_initrd_fs_exec_probe.elf`) | present via shared-storage symlink (`build/os/fat32-x86_32.img`) |
| x86_64 | present via shared-storage symlink (`build/os/simpleos_x86_64_fs_exec.elf`) | present via shared-storage symlink (`build/os/fat32-x86_64.img`) |
| ARM32 | present (`build/os/simpleos_arm32_fs_exec.elf`) | present via shared-storage symlink (`build/os/fat32-arm32.img`) |
| ARM64 | diagnostic kernel present under shared storage | present via shared-storage symlink (`build/os/fat32-arm64.img`) |
| RISC-V32 | present (`build/os/simpleos_riscv32_smf_fs.elf`) | present via shared-storage symlink (`build/os/fat32-riscv32.img`) |
| RISC-V64 | present (`build/os/simpleos_riscv64_smf_fs.elf`) | present via shared-storage symlink (`build/os/fat32-riscv64.img`) |

The focused receipt spec executed 5/5, but `readlink -f bin/simple` resolved to `bin/release/x86_64-unknown-linux-gnu/simple` and `--version` printed the Rust bootstrap-seed warning. Under repository policy this is diagnostic evidence only.

## Unblock conditions

1. Deploy a current pure-Simple Stage 4 CLI and record its path/hash/version without the seed warning.
2. Build fresh six-architecture kernels and filesystem images from the same admitted source/compiler lineage.
3. Store large media beneath `/mnt/data/.simple/qemu/images` and expose canonical descriptor paths without copying the data back to btrfs.
4. Add real guest boot/mount/listing/program markers and populate `SosixQemuGuestFilesystemReceipt` from retained transcripts.

Linux/RISC-V32 now has a complete diagnostic guest flow: QEMU exits
successfully, enumerates ten real FAT32 `/SYS/APPS` entries, loads an executable
RV32 ELF from the filesystem, captures its target-UART stdout, and observes its
zero return. The row remains blocked rather than release PASS because the kernel
was cross-built by the bootstrap seed and the transcript lacks run-nonce
correlation. See
`riscv32_qemu_guest_ls_and_program_execution_gap_2026-08-11.md`.

Linux/ARM32 also has a complete diagnostic guest flow: QEMU exits zero,
enumerates ten real FAT32 `/SYS/APPS` entries, loads and executes an ARM ELF
from the filesystem, captures target-UART stdout, and observes return zero. It
remains blocked on admitted pure-Simple compiler lineage and run-nonce
correlation; see
`arm32_qemu_release_lineage_and_nonce_gap_2026-08-11.md`.

Linux/x86_64 has a complete diagnostic guest flow as well: multiboot, NVMe
FAT32 mount, ten-entry target-side listing, filesystem-loaded execution, target
UART stdout, return zero, and `TEST PASSED`. Its QEMU exit 1 is the expected
`isa-debug-exit` success encoding. Release remains blocked on admitted
pure-Simple compiler lineage, clean source identity, and nonce correlation; see
`x86_64_qemu_release_lineage_nonce_and_clean_source_gap_2026-08-11.md`.

Linux/x86_32 now has the same complete diagnostic flow over its FAT32 initrd:
ten target-side entries, filesystem-loaded ELF32 execution, target UART stdout,
return zero, and `TEST PASSED`. It remains blocked on admitted pure-Simple
compiler lineage, clean-source identity, and nonce correlation; see
`x86_32_qemu_release_lineage_nonce_and_clean_source_gap_2026-08-11.md`.

## Resume commands

```text
scripts/qemu/simple-qemu-settings.shs --check
scripts/qemu/simple-qemu-settings.shs --prepare
bin/simple test test/01_unit/os/sosix/qemu_guest_filesystem_receipt_spec.spl --no-session-daemon --timeout 180
sh scripts/check/check-sosix-qemu-matrix.shs --guest x86_64 --preflight
```

After fresh media generation, run each `test/03_system/os/qemu/sys_qemu_<arch>_fs_exec_spec.spl` exactly once, then the planned aggregate `scripts/check/check-sosix-qemu-matrix.shs --host linux --all-guests` after it lands.

## Retained artifacts

- Storage root: `/mnt/data/.simple/qemu`
- Planned per-run root: `/mnt/data/.simple/qemu/artifacts/sosix-qemu/<host>/<guest>/<run-id>/`
- Current diagnostic output: terminal receipt in the originating SPipe session; no production PASS artifact claimed.
- Fresh x86_64 selection receipt: `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/matrix/20260811T043920Z/matrix.env` (Linux/KVM; blocked only by `build/os/simpleos_x86_64_fs_exec.elf`).
- RISC-V32 diagnostic boot receipt: `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/riscv32/20260811T050100Z/evidence.env`; serial transcript is adjacent. It is explicitly not target-`ls` or program-execution proof.
- RISC-V32 complete diagnostic guest-flow receipt: `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/riscv32/20260811T052000Z/evidence.env`; adjacent serial proves real directory enumeration and filesystem-loaded RV32 execution. It is not release PASS because compiler lineage and nonce correlation remain open.
- RISC-V64 complete diagnostic guest-flow receipt: `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/riscv64/20260811T054000Z/evidence.env`; adjacent serial proves real directory enumeration and filesystem-loaded RV64 execution. It has the same compiler-lineage and nonce-correlation release blockers.
- ARM64 failed receipt: `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/arm64/20260811T064000Z/evidence.env`; boot and mount succeed, but the present root `FSEXEC.ELF` reads as zero bytes and the kernel contains 108 fabricated stubs. See `arm64_qemu_dynamic_root_dirent_and_fabricated_stubs_2026-08-11.md`.
- ARM32 complete diagnostic guest-flow receipt: `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/arm32/20260811T074500Z/evidence.env`; adjacent serial proves real directory enumeration, filesystem-loaded ARM execution, target UART output, guest return zero, and QEMU exit zero. It is not release PASS because compiler lineage and nonce correlation remain open.
- x86_64 complete diagnostic guest-flow receipt: `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/x86_64/20260811T083000Z/evidence.env`; adjacent serial proves real directory enumeration, filesystem-loaded x86_64 execution, target UART output, guest return zero, and expected `isa-debug-exit` completion. Compiler lineage, clean-source identity, and nonce correlation remain release blockers.
- x86_32 complete diagnostic guest-flow receipt: `/mnt/data/.simple/qemu/artifacts/sosix-qemu/linux/x86_32/20260811T090000Z/evidence.env`; adjacent serial proves real FAT32 initrd enumeration, filesystem-loaded ELF32 execution, target UART output, guest return zero, and expected `isa-debug-exit` completion. Compiler lineage, clean-source identity, and nonce correlation remain release blockers.
- FreeBSD host-QEMU prerequisite receipt: `/mnt/data/.simple/qemu/artifacts/freebsd-host/20260811T090000Z/smoke.log`; tools and SSH key pass, but the FreeBSD 14.4 base image is absent, so boot/SSH/bootstrap are unproven. Resume with the same isolated environment and `sh scripts/check/check-freebsd-bootstrap-qemu.shs --smoke --download` once the image is supplied through an allowed download mechanism.

## Ownership

- Owner: SOSIX/QEMU integration lane
- Final reviewer: independent normal/highest-capability reviewer
