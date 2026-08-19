# UP2 UEFI GRUB Multiboot2 transition does not reach the kernel entry

Status: OPEN — loader transition implementation required

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

Next design decision: either implement a small admitted ELF32 Multiboot2 loader
shim that loads the ELF64 kernel and performs the reviewed 32→64 transition, or
provide a native x64 UEFI PE entry that exits boot services and enters a
UEFI-aware 64-bit kernel path. Do not claim physical UP2 boot until OVMF and the
board both reach the ordered kernel markers.
