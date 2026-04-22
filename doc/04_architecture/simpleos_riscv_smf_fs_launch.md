<!-- codex-impl -->
# SimpleOS RISC-V SMF Filesystem Launch Architecture

The RISC-V SMF filesystem launch path is a thin acceptance slice over the existing VirtIO-BLK/FAT32 probe in `examples/simple_os/arch/riscv{32,64}/boot/baremetal_stubs.c`.

The host image builder seeds architecture-specific ELF marker payloads, wraps them as SMF files, and places them under `/SYS/APPS`. The RISC-V smoke entries call boot-stub probes that walk `SYS/APPS`, read the first SMF sector, and validate both the SMF signature and architecture marker. GUI app loading is represented as a window-manager handoff marker for `/sys/apps/browser_demo.smf`; full per-process GUI rendering remains out of scope.

