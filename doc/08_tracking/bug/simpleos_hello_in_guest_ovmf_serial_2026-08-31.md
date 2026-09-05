# SimpleOS x86_64 hello-world in-guest — literal OVMF serial transcript

Captured 2026-08-31 by `scripts/check/check-simpleos-hello-world-in-guest-ovmf.shs`.
Boot chain: OVMF pflash -> GRUB-EFI -> multiboot1. No `-kernel`, no isa-debug-exit.
Kernel and payload both built by the Rust seed. L1-L5 green; L6/L7 blocked by B12.

Stored as `.md` because `.gitignore:69` (`*.log`) silently swallows a `.log` here.
Repeated `[fault]` frames elided; the single early-boot frame is retained in the
raw capture at `build/os/hello/lane/hello_in_guest_ovmf.serial.log`.

```
[2J[01;01H[=3h[2J[01;01H[2J[01;01H[=3h[2J[01;01H[2J[01;01H[=3h[2J[01;01HBdsDxe: loading Boot0001 "UEFI Misc Device" from PciRoot(0x0)/Pci(0x3,0x0)
BdsDxe: starting Boot0001 "UEFI Misc Device" from PciRoot(0x0)/Pci(0x3,0x0)
[grub-uefi] multiboot loading /boot/kernel.elf ...
WARNING: no console will be available to OS
error: no suitable video mode found.
[BOOT32] entry
[BOOT64] entry
[BOOT64] idt
[heap] alloc sz=0x100020 off_before=0x594bb0 caller=0x80069a2
[heap] alloc off_after=0x694bd0
[heap] alloc sz=0x200000 off_before=0x694bd0 caller=0x8009f16
[heap] alloc off_after=0x894bd0
[BOOT64] call _start

=== SimpleOS x86_64 hello-world in-guest (OVMF) ===
[arch-init] installing rich fault hook
[arch-init] rich fault hook installed
[BOOT] WARNING: No HHDM response from Limine
[BOOT] No RSDP from Limine (ACPI unavailable)
[arch-init] scheduler topology probed
[arch-init] syscall install begin
[syscall] MSRs programmed: LSTAR STAR SFMASK=0x200
[arch-init] EFER.NXE enabled
[arch-init] syscall install returned

[tss] rsp0 installed sel=0x30
[hello] arch-init + syscall MSRs + TSS done
[nvme-c] BAR0=0xffffc00000004000 (phys=0xc000004000)
[nvme-c] CAP=0x4018200f0107ff
[nvme-c] Admin queues configured: SQ=0x90c0000 CQ=0x90c1000
[nvme-c] NS1: sectors=1833, sector_size=512
[nvme-c] Sector 0 read OK, first bytes: EB 58 90 53 49 4D 50 4C 45 4F 53 00 02 40 20 00
[nvme-c] FAT32 signature at offset 510: 0x0xaa55
[hello] nvme online
[fat32-c] BPS=0200 SPC=40 reserved=20 FATs=01 FAT_size=09 root_cluster=02 data_start=29
[hello] /FSEXEC.ELF read size=13800 buf=0x1209897344
[PMM] Initializing scalar identity memory manager...
[PMM] scalar init complete
[VMM] Initializing virtual memory manager...
[VMM] portable VMM published kernel PML4 0x335609856
[VMM] PML4 at physical 0x335609856
[VMM] Identity-mapping first 4GB...
[VMM] Identity-mapped 4GB with 2MB pages (2048 entries)
[VMM] VMM initialization complete
[hello] pmm+vmm online
[hello] entering ring 3 ...
[spawn] parsed entry=0x4194304
[spawn] user AS ready (private low) root=335634432
[spawn] phoff=64 phentsize=56 phnum=4 use_stream=0
[spawn] image span lo=0x4194304 hi=0x5320704
[spawn] PT_LOAD segments mapped
[spawn] frame argc readback=1 expected=1
[spawn] user stack mapped top=0x549757911040 pages=2048 rsp=0x549757910912
[spawn] entering user cs=0x2b iopl=3 rip=0x4194304 rsp=0x549757910912
ABC
```
