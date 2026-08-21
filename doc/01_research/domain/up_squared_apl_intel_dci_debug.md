# Domain research: Intel DCI, UP Squared debug, boot, and storage

Date: 2026-08-21

## What DCI provides

Intel describes Direct Connect Interface (DCI) as proprietary debug technology.
Depending on product and endpoint, USB DCI can expose DFx/JTAG run control,
trace, kernel-mode debug, and DMA to or from system memory. Intel explicitly
warns that not every product implements every endpoint. Apollo Lake is listed
for the USB 3.x Debug Class connection in Intel's Target Connection Agent
matrix. Thus original UP2 can conditionally debug over USB in a JTAG-like way,
but connector presence alone proves nothing.

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

A genuine SuperSpeed debug cable is required. A normal USB A-to-A cable, USB
file-transfer/KVM bridge, phone data cable, and Tigard are not substitutes.
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

The current SimpleOS ELF has three `PT_LOAD` ranges. File bytes occupy
`0x08000000..0x0800608a`, while the final writable segment has a memory size of
`0x0180d000`; its BSS/heap/stack tail must be zeroed through approximately
`0x09813000`. The entry is `0x08000038`. This makes “write the 37,280-byte ELF
and set RIP” specifically incorrect: ELF file offsets differ from physical
addresses and roughly 24 MiB of zero-fill state is part of the image contract.

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

Linux xHCI Debug Capability can expose a high-speed serial/GNU-remote-debug
transport over a SuperSpeed debug cable after target software initializes the
controller. It is an attractive future SimpleOS console/KGDB-like backend, but
it cannot replace proprietary pre-boot DCI run control, reset, or arbitrary
physical-memory access.

## Operational safety

DCI can bypass normal isolation through run control and DMA. Use only on a
physically controlled lab target with no secrets, retain exact receipts, never
unplug while halted, and disable debug consent after testing. Intel notes that
disconnecting a halted target can lose context and crash it.

## Primary sources

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
- [UP Squared specifications](https://up-board.org/upsquared/specifications/)
- [Linux xHCI debug capability](https://cdn.kernel.org/doc/html/latest/driver-api/usb/usb3-debug-port.html)
- [Linux xHCI DbC source](https://github.com/torvalds/linux/blob/master/drivers/usb/early/xhci-dbc.h)
- [Intel Slim Bootloader ELF/Multiboot loader](https://github.com/slimbootloader/slimbootloader/blob/master/PayloadPkg/OsLoader/OsLoader.c)
- [Microsoft USB 3 debug-cable setup](https://github.com/MicrosoftDocs/windows-driver-docs/blob/staging/windows-driver-docs-pr/debugger/setting-up-a-usb-3-0-debug-cable-connection.md)
- [UP community DCI discussion](https://forum.up-community.org/discussion/3701/dci-debug-for-upsquared) (community evidence)
- [UP community firmware compatibility discussion](https://forum.up-community.org/discussion/4806/opensource-uefi-bios-by-intel-appears-to-be-unusable-now) (community evidence)
