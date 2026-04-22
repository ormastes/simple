<!-- codex-impl -->
# SimpleOS RISC-V SMF Filesystem Launch Test Plan

- Unit: `test/unit/os/qemu_runner_spec.spl` checks RV32/RV64 scenario registration, disk paths, QEMU args, target entries, and timeouts.
- Image: `scripts/make_os_disk.shs 64 build/os/fat32-riscv64.img "" riscv64` and `riscv32` must include CLI and GUI payload markers.
- Live boot: `scripts/qemu_riscv64.shs --fs-image` and `scripts/qemu_riscv32.shs --fs-image` must find all stable serial markers when an LLVM-enabled compiler and QEMU are available.
- Verified locally on 2026-04-22: both script live boots reported `=== Results: 9 passed, 0 failed ===` and `TEST PASSED`.
