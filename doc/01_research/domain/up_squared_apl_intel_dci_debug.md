# Domain research: Intel DCI, UP Squared debug, boot, and storage

Date: 2026-08-21

## What DCI provides

Intel describes Direct Connect Interface (DCI) as proprietary debug technology.
Depending on product and endpoint, USB DCI can expose DFx/JTAG run control,
trace, kernel-mode debug, and DMA to or from system memory. Intel explicitly
warns that not every product implements every endpoint. Apollo Lake is listed
for the USB 3.x Debug Class connection in Intel's Target Connection Agent
matrix. Thus Apollo Lake silicon has a conditional JTAG-like USB lane.
Applicability to an original UP2 still requires proof for the exact FAB, BIOS
routing/consent, cable, and physical connection; connector presence proves none
of those conditions.

The supported software path is Intel System Debugger/System Bring-Up Toolkit
through Target Connection Agent. Current toolkit access requires an Intel CNDA,
and detailed target guides are controlled. Public release notes document
physical-memory viewing, root-CPU warm reset, and power-good reset controls,
but do not publish a complete Apollo Lake arbitrary-ELF boot recipe.

An Apollo Lake exception is decisive: Intel System Debugger 2020 release notes
state that **OpenRC warm reset on Apollo Lake can leave the target in an
undefined state with cores that cannot be released**. Intel lists no software
workaround and requires manual target reset to recover. A generic “DCI software
reset” must therefore not be the default UP2 recovery operation. A toolkit
Power-Good reset may be evaluated separately, but only retained physical
evidence on the exact board can qualify it.

## Hardware and firmware gates

A genuine Intel-qualified DCI DbC cable/probe is required. A normal USB A-to-A
cable, USB file-transfer/KVM bridge, phone data cable, and Tigard are not substitutes.
Debug cables are purpose-built and must not source ordinary VBUS between hosts.

Community UP2 reports identify firmware controls such as `DCI Enable (HDCIEN)`,
Platform Debug Consent, and Advanced Debug/DCI Enable. The exact menu varies by
BIOS. Run control also depends on the architectural `IA32_DEBUG_INTERFACE`
state being enabled and not locked against the desired mode. These are
diagnostic conditions, not permission to patch an MSR or flash firmware.

Intel published old FAB-A UP2 debug/release firmware, but community reports
include incompatible revisions, one-way conversions, and recovery requiring an
SPI programmer. No firmware image should be flashed without exact FAB matching,
backup, recovery hardware, image validation, and explicit authorization.

## DCI load and boot contract

DCI memory access can stage bytes, but booting an ELF also requires the correct
CPU and platform state. A debugger-assisted boot must reserve valid DRAM, load
all ELF segments, zero BSS, control every logical processor, define GDT/IDT and
page tables, program the required CR0/CR3/CR4/EFER state, establish stack and
handoff registers, then resume the bootstrap processor. Reset state, UEFI
long-mode state, and SimpleOS `_entry32` are not interchangeable.

The lowest-risk practical lane is DCI-assisted UEFI boot: use DCI for halt,
reset, memory inspection, and breakpoints while firmware loads the existing
UEFI USB image. A direct DCI RAM boot needs a small reviewed trampoline designed
for the exact debugger entry state. It remains blocked until the proprietary
toolchain and physical cable are present.

The current SimpleOS ELF has three `PT_LOAD` ranges. Its last file-backed byte
ends at physical `0x080290fa`, while the final writable segment has a memory
size of `0x02fd7000`; its BSS/heap/stack/staging tail ends at `0x0b000000`.
The entry is `0x08000038`. This makes “write the 225,152-byte ELF
and set RIP” specifically incorrect: ELF file offsets differ from physical
addresses and nearly 48 MiB of zero-fill state is part of the image contract.

Intel Slim Bootloader provides public precedent for the safer architecture: its
OS loader parses ELF and Multiboot/Multiboot2 images, loads segments, constructs
boot information, and jumps through a defined boot-state transition. For UP2,
the existing UEFI/GRUB plus reviewed Multiboot2 shim already performs that role.
A future DCI mailbox should stage bytes into a buffer and let a resident,
target-side loader validate and perform the transition; the debugger should not
invent CPU state ad hoc.

## Storage read/write

DCI is not a block-storage protocol. Staging a disk image in RAM does not safely
write eMMC, SATA/mSATA, or USB storage. Persistent writes require a target-side
driver or trusted RAM-resident Linux/provisioner that identifies one device by
model, serial, transport, capacity, partition table, mount/holder state, and
root/swap exclusion. It must write within explicit bounds, flush, detach or
remount, and hash the exact readback. Direct controller-MMIO writes through the
debugger are not an admissible provisioning method.

The original board provides eMMC and SATA/mSATA. Its M.2 2230 E-key is not a
generic M-key NVMe slot. A USB NVMe enclosure normally presents through USB
mass storage/UAS and must be admitted by observed identity rather than assumed
device-node spelling.

## Open xHCI DbC is a different lane

Linux xHCI Debug Capability can expose a high-speed bidirectional byte transport
over a SuperSpeed debug cable after target software initializes the controller.
Its GNU Remote Debug interface descriptor does not itself implement CPU debug;
a resident RSP/KGDB agent is still required. It is an attractive future
SimpleOS console/KGDB-like backend, but
it cannot replace proprietary pre-boot DCI run control, reset, or access to the
physical-memory regions authorized by the target's DCI implementation.

## Free and open tooling audit (2026-08-22)

No legitimate free/open-source host tool found in this audit implements the
Apollo Lake DCI control plane. Intel describes USB DCI as a closed,
Intel-proprietary ExI protocol with product-dependent DFx/JTAG run control,
trace, kernel-mode-debug, and DMA endpoints. The only documented independent
full-DCI host is Lauterbach TRACE32, which requires licensed x86/x64 frontend
and DCI.DbC backend products; it is an alternative to Intel System Debugger,
but not a free one.

| Free component | What it can do | Earliest availability | Not provided |
|---|---|---|---|
| SimpleOS target GDB RSP monitor | bounded `m`/`M` memory access with checksum and write readback | after SimpleOS and the UART monitor start | registers, breakpoints, step/continue/reset, pre-agent halt, silicon trace, autonomous DMA |
| Linux KGDB/KDB | Linux kernel source debug over an initialized console | after Linux KGDB and its I/O driver start | UEFI/SEC/PEI or dead-target recovery |
| Linux xHCI DbC | early-printk/runtime high-speed bidirectional TTY | after target xHCI DbC initialization | Intel DCI JTAG/run control/reset/DMA |
| CHIPSEC | privileged live physical-memory, PCI/MMIO, and firmware inspection | after its Linux/Windows driver or UEFI agent starts | halt/step/breakpoints and external recovery |
| EDK II SourceLevelDebugPkg | resident IA32/X64 SEC/PEI/DXE/SMM debug agents over serial/USB | after a safely integrated agent starts | instrumentation of stock UP2 firmware or Intel DCI |
| OpenOCD | supported open target transports and cores | only for targets it implements | Apollo Lake DCI; its documented Intel x86 target is Quark, not Apollo Lake |

The practical free UP2 sequence is therefore UEFI removable-media boot, CN16
UART logging, and a future target-side SimpleOS GDB stub. xHCI DbC can later
replace UART as the byte transport, but it cannot promote that software debug
session to DCI evidence. CHIPSEC is useful only when a trusted OS/UEFI agent is
already executing on UP2 and must not be installed on the host under the false
assumption that it can reach a remote board.

## Operational safety

DCI can bypass normal isolation through run control and DMA. Use only on a
physically controlled lab target with no secrets, retain exact receipts, never
unplug while halted, and disable debug consent after testing. Intel notes that
disconnecting a halted target can lose context and crash it.

## Primary-source capability audit (2026-08-22)

Intel's public Target Connection Agent matrix explicitly lists Apollo Lake
N4200, N3350, x7-E3950, and x5-39xx under **DCI USB 3.x Debug Class**. This is
stronger than a generic processor-family inference, but it proves only that the
silicon/tool combination is supported. It does not identify which original-UP2
receptacle is routed for DCI, prove firmware consent, or prove that every DCI
endpoint is exposed. Intel separately states that endpoint availability is
product-dependent.

Intel's current toolkit page still requires a signed corporate CNDA and an
authenticated Registration Center download. An Intel support answer from 2025
states that it is not available for private/individual use. Therefore there is
no legitimate free installer to automate on this host; open tools can implement
target-resident software debugging but cannot decode Intel's proprietary ExI
run-control transport.

UEFI 2.10 defines two useful but narrower mechanisms. The Debug Support and
Debug Port protocols let a resident debug agent receive exception contexts and
use a serial-like transport. The Debug Support Table gives an external hardware
debugger a quiescent, memory-only route to the EFI system table and loaded-image
database, beginning from a structure on a 4 MiB-aligned address. These improve
symbol discovery after compliant firmware publishes them; they do not allocate
a DCI mailbox, authenticate an ELF, or perform an OS handoff. A resident loader
still must be built and executed explicitly.

The original UP Squared manual identifies CN7 as M.2 E-key, CN8 as Mini Card,
CN9/CN10 as SATA/data power, CN13 as USB3 OTG port 0, CN14 as USB3 ports 1/2,
CN15 as USB3 port 3, CN16 as the
USB/UART panel, and CN22 as CPLD/BIOS update. It documents no native M-key NVMe
socket. A physical NVMe connected through an adapter is accepted only if PCI
enumeration reports class/subclass `01:08` and NVMe Identify succeeds; connector
shape or an adapter label is not evidence.

Linux documentation says the DbC-capable receptacle is normally the first
SuperSpeed port, but that does not prove CN13 is DCI on UP2. Discover the exact
port through the Intel tool and a live connection; do not prescribe CN13 from
port numbering alone.

## Primary sources

## Free-tool conclusion and live cable qualification (2026-08-22)

The legitimate no-cost host stack is GNU GDB/GDB multiarch plus OpenOCD for
supported probes, and picocom for CN16 UART. It does **not** implement Intel
DCI: Intel describes DCI run control and memory DMA as a closed, proprietary
ExI transport, while OpenOCD's documented Intel target support is Intel Quark,
not Apollo Lake DCI. A target-resident GDB Remote Serial Protocol stub remains
the free route for SimpleOS memory read/write after boot.

The attached `0ea0:2211` Smart KM Link was descriptor-qualified as USB 2.0 with
only SCSI mass-storage, HID mouse, and HID keyboard interfaces. It exposes no
CDC/ACM UART, FTDI interface, USB 3.x Debug Capability, or Intel DCI endpoint.
An OpenOCD probe with the packaged Tigard configuration failed at FTDI discovery
because `0403:6010` is absent. This is a missing physical debug transport, not a
permissions or target-configuration failure. Community UP2 reports also warn
that DCI appeared only in some BIOS revisions and could connect/reset without
reliable halt, so exact-board physical qualification remains mandatory.

- [Intel Debug Technology](https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/secure-coding/intel-debug-technology.html)
- [Intel Target Connection Agent](https://www.intel.com/content/www/us/en/developer/articles/technical/isd-easily-configureconnect-to-different-hw-platforms-via-tca-target-connection-agent.html)
- [Intel System Bring-Up Toolkit](https://www.intel.com/content/www/us/en/developer/tools/oneapi/system-bring-up-toolkit.html)
- [Intel System Bring-Up Toolkit release notes](https://www.intel.com/content/www/us/en/developer/articles/release-notes/intel-system-bring-up-toolkit-release-notes.html)
- [Intel System Bring-Up Toolkit requirements](https://www.intel.com/content/www/us/en/developer/articles/system-requirements/intel-system-bring-up-toolkit-system-requirements.html)
- [Intel System Debugger 2019 Linux release notes](https://www.intel.com/content/dam/develop/external/us/en/documents/system-debug-2019-linux-release-notes-797773.pdf)
- [Intel System Debugger 2020 Linux release notes](https://www.intel.com/content/dam/develop/external/us/en/documents/public-2020initialrelease-lin-797773.pdf)
- [Intel E3900 UP2 UEFI firmware project](https://www.intel.com/content/www/us/en/developer/articles/tool/uefi-firmware-project-for-intel-atom-processor-e3900-series-processor-platforms.html)
- [Intel Software Developer Manuals](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)
- [UP Squared user manual download](https://downloads.up-community.org/download/up-squared-user-manual/)
- [UP Squared original-board manual, 5th edition](https://up-shop.org/media/productattach/u/p/up_squared_ups-apl_manual_5th_ed_0716c.pdf)
- [UP Squared specifications](https://up-board.org/upsquared/specifications/)
- [Zephyr UP Squared UEFI boot instructions](https://docs.zephyrproject.org/latest/boards/up-bridge-the-gap/up_squared/doc/index.html)
- [Linux xHCI debug capability](https://cdn.kernel.org/doc/html/latest/driver-api/usb/usb3-debug-port.html)
- [GDB remote-stub requirements](https://sourceware.org/gdb/current/onlinedocs/gdb.html/Remote-Stub.html)
- [GDB remote protocol packets](https://sourceware.org/gdb/current/onlinedocs/gdb.html/Packets.html)
- [Linux KGDB/KDB](https://docs.kernel.org/process/debugging/kgdb.html)
- [CHIPSEC](https://github.com/chipsec/chipsec)
- [CHIPSEC physical-memory utility](https://chipsec.github.io/modules/chipsec.utilcmd.mem_cmd.html)
- [EDK II SourceLevelDebugPkg](https://github.com/tianocore/edk2/blob/master/SourceLevelDebugPkg/SourceLevelDebugPkg.dsc)
- [OpenOCD Intel architecture support](https://openocd.org/doc/html/Architecture-and-Core-Commands.html#Intel-Architecture)
- [TRACE32 Intel DCI support](https://www.lauterbach.com/products/software/debugging-via-usb)
- [TRACE32 DCI.DbC backend license](https://www.lauterbach.com/products/LA-8971L)
- [Linux xHCI DbC source](https://github.com/torvalds/linux/blob/master/drivers/usb/early/xhci-dbc.h)
- [Intel Slim Bootloader ELF/Multiboot loader](https://github.com/slimbootloader/slimbootloader/blob/master/PayloadPkg/OsLoader/OsLoader.c)
- [UEFI 2.10 debugger-support protocols and loaded-image table](https://uefi.org/specs/UEFI/2.10_A/18_Protocols_Debugger_Support.html)
- [UEFI 2.10 boot services and memory-map transition](https://uefi.org/specs/UEFI/2.10_A/07_Services_Boot_Services.html)
- [Intel support: toolkit unavailable for individual use](https://community.intel.com/t5/oneAPI-Registration-Download/How-to-get-download-Intel-System-Bring-up-Toolkit/td-p/1694982)
- [Microsoft USB 3 debug-cable setup](https://github.com/MicrosoftDocs/windows-driver-docs/blob/staging/windows-driver-docs-pr/debugger/setting-up-a-usb-3-0-debug-cable-connection.md)
- [UP community DCI discussion](https://forum.up-community.org/discussion/3701/dci-debug-for-upsquared) (community evidence)
- [UP community firmware compatibility discussion](https://forum.up-community.org/discussion/4806/opensource-uefi-bios-by-intel-appears-to-be-unusable-now) (community evidence)
