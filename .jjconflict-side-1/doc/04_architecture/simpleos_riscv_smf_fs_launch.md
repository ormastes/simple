<!-- codex-impl -->
# SimpleOS RISC-V SMF Filesystem Smoke Architecture

The RISC-V SMF filesystem lane is a bounded smoke slice over the existing VirtIO-BLK/FAT32 reader in `examples/simple_os/arch/riscv{32,64}/boot/baremetal_stubs.c`.

The host image builder seeds architecture-specific ELF marker payloads, wraps them as SMF files, and places them under `/SYS/APPS`. The RISC-V smoke entries call boot-stub loaders that walk `SYS/APPS`, read the complete SMF file, unwrap the embedded ELF payload, validate RISC-V program headers, and copy PT_LOAD bytes into a synthetic probe arena.

This lane does not prove kernel/VFS/process-backed hosted execution. Hosted proof is tracked separately under `simpleos_rv64_hosted_qemu`.
