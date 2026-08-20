# UP2 UEFI GRUB Multiboot2 transition does not reach the kernel entry

Status: RESOLVED (2026-08-20) — ELF32 shim reaches the ELF64 kernel entry

The exact UP2 removable image is discovered and started by OVMF. Its standalone
GRUB emits `UP2 loader-ready`, accepts the structurally validated ELF64
Multiboot2 kernel, and emits `UP2 kernel-admitted`. After `boot`, CPU0 never
reaches `_entry32` at the ELF entry near `0x08000500`; no `[BOOT32] entry` byte
appears.

Earlier Multiboot1 packaging was invalid for this ELF64 contract and entered
garbage low memory. The kernel now carries a valid Multiboot2 header alongside
the retained legacy Multiboot1 header, and the removable image uses
`multiboot2`. This closes image admission but not the UEFI transition.

GDB/QEMU evidence after GRUB admission shows the kernel is present at physical
`0x08000000`, while CPU0 remains in invalid low transition memory instead of
the ELF entry. Single-vCPU execution removes the unrelated AP-startup fault but
does not change the result.

Retained evidence:

- `build/test-artifacts/03_system/os/x86_64/up_squared_apl_simpleos/ovmf-loader-markers-20260820/uart.log`
- `build/test-artifacts/03_system/os/x86_64/up_squared_apl_simpleos/ovmf-multiboot2-gdb-smp1-20260820/uart.log`

Resolution: the removable image now boots a bounded ELF32 Multiboot2 shim,
passes the admitted ELF64 kernel as a named module, validates its ELF class,
machine, program headers, segment bounds, and low physical addresses, copies
its `PT_LOAD` segments, and jumps to the normalized `_entry32` ELF entry. OVMF
evidence reaches `[UP2-SHIM] elf64-loaded`, `[BOOT32] entry`, and `[BOOT64]
entry`. This resolves the firmware/loader transition only. The subsequent
ring-0 runtime closure is tracked separately, and physical UP2 boot remains
unproven until the board reaches the ordered kernel and command-correlated
`ls /` markers.
