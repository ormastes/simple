<!-- codex-impl -->
# SimpleOS RISC-V SMF Filesystem Launch Design

Implementation touches four surfaces:

- `scripts/make_os_disk.shs` creates RV32/RV64 CLI and GUI ELF marker fixtures and SMF wrappers.
- RISC-V boot stubs add `rt_riscv_smf_cli_probe` and `rt_riscv_smf_gui_probe`, reusing the existing FAT32 directory traversal.
- RISC-V smoke entries emit the stable filesystem, SMF discovery, CLI launch, WM GUI launch, and pass markers.
- `src/os/qemu_runner.spl` exposes `riscv64-virtio-fat32-smf` and `riscv32-virtio-fat32-smf` scenarios with platform disk paths and arch-local build source roots.

Failure mode: missing image markers fail in host-side validation; missing runtime SMF markers print `TEST FAILED`.
