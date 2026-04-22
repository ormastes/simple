<!-- codex-impl -->
# SimpleOS RISC-V SMF Filesystem Launch Architecture

The RISC-V SMF filesystem launch path is a native acceptance slice over the existing VirtIO-BLK/FAT32 reader in `examples/simple_os/arch/riscv{32,64}/boot/baremetal_stubs.c`.

The host image builder seeds architecture-specific ELF marker payloads, wraps them as SMF files, and places them under `/SYS/APPS`. The RISC-V smoke entries call boot-stub loaders that walk `SYS/APPS`, read the complete SMF file, unwrap the embedded ELF payload, validate RISC-V program headers, and copy PT_LOAD bytes into a per-process native arena. GUI app loading uses the same process load path and reports a process-owned native render surface marker for `/sys/apps/browser_demo.smf`.
