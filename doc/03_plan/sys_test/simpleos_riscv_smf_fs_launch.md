<!-- codex-impl -->
# SimpleOS RISC-V SMF Filesystem Launch Test Plan

- Unit: `test/unit/os/qemu_runner_spec.spl` checks RV32/RV64 scenario registration, disk paths, QEMU args, target entries, and timeouts.
- Image: `scripts/make_os_disk.shs 64 build/os/fat32-riscv64.img "" riscv64` and `riscv32` must include CLI and GUI payload markers.
- Live boot: `scripts/qemu_riscv64.shs --fs-image` must find all stable serial markers plus the x86_64 desktop-shell process-backed marker for `/sys/apps/browser_demo.smf`.
- Shared-service boot: `scripts/qemu_riscv64.shs --fs-image --shared-service` verifies the shared desktop app ownership contract used by the x86_64 launcher/WM path.
- Follow-up boot: `scripts/qemu_riscv32.shs --fs-image` must keep the existing RV32 filesystem SMF smoke markers passing.
- Verified locally on 2026-04-22: RV64 and RV32 runtime checks passed with `--skip-build` against existing kernels after rebuilding the FAT32 images. RV64 reported `=== Results: 12 passed, 0 failed ===`; RV32 reported `=== Results: 11 passed, 0 failed ===`; both ended with `TEST PASSED`.
- Verified locally on 2026-04-22 after rebuilding `src/compiler_rust/target/debug/simple` with the Rust `llvm` feature: `scripts/qemu_riscv64.shs --fs-image --shared-service` reported `=== Results: 12 passed, 0 failed ===` and `TEST PASSED`.
