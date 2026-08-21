# Local research: Intel DCI debugging on original UP Squared

Date: 2026-08-21

## Scope and repository state

This research is specific to original `UPS-APL` Apollo Lake boards. It does not
generalize to UP Squared Pro, V2, 6000, or later products. The existing
SimpleOS lane currently builds a 225,152-byte freestanding ELF and 256 MiB
GPT/FAT32 UEFI image. Its OVMF oracle reaches the loader, 32-bit shim, 64-bit entry, console,
VFS, shell, and a command-correlated `ls /` containing `/bin`, `/etc`, and
`/README.txt`. That is host-side firmware evidence, not a physical-board PASS.

The current kernel ELF enters through `_entry32` at `0x08000038`. Its bootstrap
expects the Multiboot-style 32-bit protected-mode contract and then establishes
paging and long mode. Copying the ELF into RAM and setting RIP from an arbitrary
UEFI/debugger state would violate that contract. A DCI loader must load every
`PT_LOAD`, zero BSS, park other cores, reserve non-firmware RAM, construct the
handoff, and establish the documented control-register, segment, stack, and
entry state before resuming exactly one bootstrap processor.

The artifact's three loadable ranges are:

| File offset | Physical address | File size | Memory size | Flags |
|---:|---:|---:|---:|:---|
| `0x1000` | `0x08000000` | `0x026719` | `0x026719` | R-X |
| `0x28000` | `0x08027000` | `0x001f9a` | `0x001f9a` | R-- |
| `0x2a000` | `0x08029000` | `0x0000fa` | `0x02fd7000` | RW- |

Consequently, a direct loader must zero the last segment beyond its 250 file
bytes through `0x0b000000`. Loading the ELF file contiguously is not loading
the program image.

## Connected-host inventory

The connected Smart KM Link `0ea0:2211` is a USB 2.0 composite mass-storage and
HID keyboard/mouse bridge. Its small `SmartKMLink` CD image is read-only. It is
not a USB 3.x DbC cable and does not expose Intel DCI.

The Tigard `0403:6010` is an FT2232H UART/JTAG adapter. It remains useful for
CN16 3.3 V TTL UART. Original-UP2 CN22 is a CPLD/BIOS service header whose pin 4
is 1.8 V and whose documented JTAG path is for the FPGA; it is not a documented
Apollo Lake CPU JTAG chain. The manual does not publish VIH/VIL limits for every
CN22 signal, so do not infer that a generic 1.8-V adapter makes the header safe.

No Intel System Debugger/System Bring-Up Toolkit, Target Connection Agent,
`99-dci.rules`, DCI device, or xHCI DbC host endpoint is installed or enumerated
on this workstation. Generic GDB/OpenOCD cannot substitute for Intel's
proprietary DCI protocol. Therefore physical DCI halt, reset, memory load, and
SimpleOS boot are currently **blocked**, not failed and not passed.

## Implementation seams

- A read-only checker may inventory USB descriptors, Intel tool presence, and
  retained debugger receipts. It must never guess DCI from an unknown VID/PID.
- A future DCI receipt must bind board model/FAB, BIOS version, connection type,
  debugger/tool version, cable identity, target power state, and the exact
  observed halt/reset/memory operation.
- A future RAM loader needs a reviewed bootstrap trampoline and a memory map
  obtained from the exact boot. It must hash-bound the admitted SimpleOS ELF and
  reject SMRAM, firmware, ACPI, MMIO, and DMA-owned ranges.
- Persistent writes must be performed by a trusted target-side USB/eMMC/SATA
  driver or a RAM-booted Linux provisioner. DCI memory DMA is only a staging
  channel; direct storage-controller MMIO pokes are outside the safe contract.

## Blockers for physical proof

1. Genuine Intel SVT DCI DbC2/3 cable/probe, or another cable explicitly
   qualified by Intel's target-connection documentation for this DCI lane.
2. Exact UP2 board FAB and current firmware identified and recoverable.
3. Firmware DCI/debug consent and `IA32_DEBUG_INTERFACE` enabled and unlocked.
4. CNDA-controlled Intel System Debugger/System Bring-Up Toolkit plus supported host.
5. A retained connection receipt proving the target, rather than a USB bridge.
6. A reviewed DCI bootstrap contract or standard UEFI media for actual boot.

Intel's published 2020 release notes add a reset blocker: Apollo Lake OpenRC
warm reset may strand cores in an undefined state, with manual reset as the only
listed recovery. No UP2 automation should select OpenRC warm reset.

## Free-tool physical trial (2026-08-22)

The Ubuntu host already had native x86 GDB; `picocom` 3.1 was installed from
Ubuntu. While Tigard was connected, its FTDI EEPROM identified interface 00 as
Port A/Serial (`/dev/ttyUSB0`) and interface 01 as Port B/JTAG
(`/dev/ttyUSB1`). Both passive 115200 captures were empty. A harmless `ls /`
probe sent to the actual serial channel at 115200 8N1, raw mode, no hardware
flow control produced zero response bytes. A subsequent five-minute serial
capture also contained zero bytes. Tigard was later disconnected and neither
`/dev/ttyUSB*` node remained.

The official CN16 wiring resolves the next operator check: pin 8 is GND, pin 9
is board UART RX, and pin 10 is board UART TX, all UART signals at 3.3-V TTL.
Connect board pin 10 to adapter RX and pin 8 to GND for a safe receive-only
test; add board pin 9 to adapter TX only for an interactive shell. Never connect
CN16 5-V pins 1 or 5 to Tigard. The required format is 115200 8N1 with no flow
control. A fresh physical reset/boot transcript is still missing, so the empty
capture does not distinguish an unpowered board, crossed/missing wiring, absent
firmware output, or a SimpleOS legacy-COM1 routing defect.

Local code review found no target-side GDB server: the existing
`src/lib/nogc_sync_mut/debug/remote/protocol/gdb_rsp.spl` is a host client, and
the UP2 IDT has no #DB/#BP register-frame/continue/step service. The xHCI driver
also lacks Debug Capability extended-register/context/ring support. The UP2
entry now explicitly initializes legacy COM1 I/O `0x3f8` before its first
marker. The shared initializer drains the `0xAE` loopback-probe byte before
normal input; otherwise the first command becomes `0xAEls /`. OVMF proves clean
boot output and `ls /` after this fix, but physical CN16 remains unproven.
The UP2 entry now initializes the shared Pure-Simple NVMe driver read-only,
prints exact Identify data, and exposes an identity-bound GPT/FAT32 provisioner.
OVMF plus QEMU NVMe proved partitioning, format, flush, fresh-adapter readback,
`ls /nvme`, and independent host `fdisk`/`mdir`/`mtype` interoperability. This
does not prove the physical adapter/drive on original UP2; the board manual has
no native M-key NVMe socket, so live PCI class `01:08` and Identify are required.

The free post-boot memory gap is now implemented without expanding DCI claims.
The linker reserves a 16 MiB writable `PT_LOAD` range at
`0x0a000000..0x0b000000`; `gdb_rsp_monitor.spl` admits only checksummed `m`/`M`
packets of at most 1024 bytes in that range, and `M` performs exact readback.
The CN16 adapter enters only after the shell command `gdb`; register,
breakpoint, continue, step, reset, and binary-write packets remain unsupported.
The admitted Stage 3 compiler built the freestanding image, and OVMF wrote
`SIMP`, read `53494d50`, detached, and returned to the shell. Physical CN16
evidence remains missing because Tigard is disconnected.

The selected resident-mailbox boot path remains incomplete. The repository has
pure admission policy (`dci_mailbox.spl`) for descriptor replay protection,
SHA-256, ELF segments, and storage bounds, but no UEFI image currently reserves
and publishes that mailbox, double-snapshots the descriptor, copies/zeros the
segments, exits boot services, parks APs, or transfers through the Multiboot2
shim. OVMF proves the existing embedded GRUB/module boot and post-boot RSP
staging range; neither is evidence of a DCI-authored preboot payload handoff.

The current image topology explains the gap: `BOOTX64.EFI` is produced by
`grub-mkstandalone`, and GRUB enters the ELF32 Multiboot2 loader only after the
UEFI application phase. Adding mailbox polling to that shim could prove a
post-UEFI RAM transport, but could not reserve pages, obtain the final UEFI
memory map, or own `ExitBootServices`; it must not be relabelled as the selected
UEFI-resident loader. The missing implementation dependency is a real x86-64
PE/COFF UEFI application using the Microsoft x64 firmware ABI plus a reviewed
transition into the existing 32-bit Multiboot shim.

The current host inventory on 2026-08-22 again exposes only Smart KM Link
`0ea0:2211`; Tigard `0403:6010`, `/dev/ttyUSB*`, Intel toolkit directories, and
a retained DCI connection are absent.

The free host tools are now complete: OpenOCD 0.12.0, GNU GDB 15.1,
`gdb-multiarch` 15.1, and picocom 3.1. `lsusb -v` proves the Smart KM Link has
only mass-storage and HID keyboard/mouse interfaces. The packaged
`interface/ftdi/tigard.cfg` probe reaches OpenOCD but returns `no device found`
for FTDI `0403:6010`. Therefore no current host tool can reach the UP2 through
the attached cable; the next physical prerequisite is CN16 3.3-V UART or a
qualified USB3 DCI cable/tool, not another software install.

Fresh current-artifact evidence on 2026-08-22 binds kernel SHA-256
`31ce1fb45630f3442b9d789068fb13db8c66412428c71cee096e00ccc4e1fbdf`
and USB-image SHA-256
`983b74b946a4b2d42e2a44f7b56eca688ad3202ff0a271827251ccc185db9ae8`.
The OVMF boot gate passed ordered firmware/loader/kernel markers, VFS-backed
`ls /`, and GDB `M`/`m` write/readback. The independent scratch-NVMe gate passed
Identify-with-zero-writes, GPT, FAT32, flush, fresh-adapter readback, and
`/nvme/proof.txt`. These replace stale emulator receipts but do not promote
physical UP2, CN16, DCI, or physical-drive evidence.

Subsequent current-source evidence supersedes those artifact hashes. Kernel
build remains 58 compiled / 0 failed; the self-contained image SHA-256 is
`9be0dd3b3e89b1be330826a216a38de820e8144dcdb60a4aa100a3cd05b2aa89`.
`--ovmf-image-provision` now passes constant-memory target SHA, scratch-NVMe
write, Flush, fresh-adapter exact readback, independent host SHA, and unchanged
adjacent ranges. `--ovmf-nvme-boot` boots that image as the sole NVMe device
with USB absent and completes VFS-backed `ls /`.

The smallest resident-loader boundary is currently C/COFF plus assembly, not a
native Simple UEFI target: Simple x86-64 codegen is SysV and has no qualified
PE32+/Microsoft-ABI personality. Clang/LLD can emit a valid EFI application,
and free `gnu-efi` headers are installed. The existing ELF32 shim can be reused
only after constructing a below-4-GiB Multiboot2 module record and performing a
reviewed post-`ExitBootServices` long-mode-to-i386 transition.

Two local blockers precede that transition. First, the Simple policy descriptor
is not a packed wire record and lacks physical pointer, endian, commit alignment,
and coherency rules. Second, kernel `_entry32` saves EBX in ESI and then reuses
ESI for a serial string before forwarding boot info; current UP2 startup ignores
the argument, masking the loss. Wire-v1 must land first, then MBI preservation
and parsing, before a resident-loader boot receipt can be trusted.

## Resident-loader implementation result (2026-08-22)

This section supersedes the earlier “blockers precede transition” status and
artifact hashes without deleting that research history. Wire-v1 is now a packed
128-byte record with an aligned commit word at offset 124. The PE32+ GNU-EFI
loader reserves fixed mailbox, payload, kernel, Multiboot-info, and embedded
shim windows; verifies nonce, stable snapshots, two exact payload hashes and
bounded non-overlapping ELF64 segments; obtains the final EFI map; exits boot
services; and enters the existing ELF32 shim through a dedicated x64-to-i386
trampoline. The EBX/ESI loss in `_entry32` is fixed.

The authoritative current kernel is 298,648 bytes with SHA-256
`0a8afd63b50bc57792d43cf6e06a643fc2d22d62e7de608b8629137c92293c08`;
the byte-reproducible 256 MiB image SHA-256 is
`abffdd3f668f075385756b1e528605950d782ee95f821bca241c13f259de93fe`.
Two fresh builds compare byte-for-byte after pinning the build epoch, GPT
disk/ESP GUIDs, FAT serial, and mtools timestamps. That exact image passed both
GRUB-fallback boot/VFS `ls /` and direct resident mailbox boot with loader PE
`2b116981…a936e` and the kernel bytes above.
`--ovmf-dci-admission` halted OVMF at reset through GNU GDB, continued to the
resident publisher, wrote the entire kernel and descriptor/commit into RAM,
and reached shim, `_entry32`, kernel, filesystem, and shell markers with no
GRUB fallback. The separate no-commit OVMF path still chainloads GRUB and passes
VFS `ls /`. These close the single-CPU software path only; physical Apollo Lake
DCI and multi-core AP parking remain open.

An attempted SMP4 OVMF MP-services rendezvous never reached mailbox publication;
the loader printed only its temporary entry diagnostic before blocking. After
three bounded audit cycles the experiment was removed rather than shipping a
multi-core regression. The retained loader/verifier stays SMP1, and physical
UP2 AP/topology evidence remains explicit.
