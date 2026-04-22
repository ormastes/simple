<!-- codex-impl -->
# SimpleOS RISC-V SMF Filesystem Launch Requirements

## Requirements

- REQ-RISCV-SMF-001: `riscv64` and `riscv32` FAT32 disk images must seed architecture-matched SMF-wrapped CLI and GUI app fixtures.
- REQ-RISCV-SMF-002: RISC-V filesystem boot smoke entries must prove the attached FAT32 image is readable before declaring success.
- REQ-RISCV-SMF-003: The boot path must discover, SMF-unwrap, ELF-validate, and load `/SYS/APPS/HELLOSMF.SMF` as the CLI executable fixture.
- REQ-RISCV-SMF-004: The boot path must discover, SMF-unwrap, ELF-validate, and load `/SYS/APPS/BROWSMF.SMF` as a GUI process fixture, then render a process-owned native GUI surface marker.
- REQ-RISCV-SMF-005: QEMU scripts and `os.qemu_runner` must expose first-class RV32/RV64 VirtIO-BLK FAT32 SMF scenarios.
