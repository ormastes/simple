# Local research: Intel DCI debugging on original UP Squared

Date: 2026-08-21

## Scope and repository state

This research is specific to original `UPS-APL` Apollo Lake boards. It does not
generalize to UP Squared Pro, V2, 6000, or later products. The existing
SimpleOS lane builds a 37,280-byte freestanding ELF and 256 MiB GPT/FAT32 UEFI
image. Its OVMF oracle reaches the loader, 32-bit shim, 64-bit entry, console,
VFS, shell, and a command-correlated `ls /` containing `/bin`, `/etc`, and
`/README.txt`. That is host-side firmware evidence, not a physical-board PASS.

The current kernel ELF enters through `_entry32` at `0x08000038`. Its bootstrap
expects the Multiboot-style 32-bit protected-mode contract and then establishes
paging and long mode. Copying the ELF into RAM and setting RIP from an arbitrary
UEFI/debugger state would violate that contract. A DCI loader must load every
`PT_LOAD`, zero BSS, park other cores, reserve non-firmware RAM, construct the
handoff, and establish the documented control-register, segment, stack, and
entry state before resuming exactly one bootstrap processor.

## Connected-host inventory

The connected Smart KM Link `0ea0:2211` is a USB 2.0 composite mass-storage and
HID keyboard/mouse bridge. Its small `SmartKMLink` CD image is read-only. It is
not a USB 3.x DbC cable and does not expose Intel DCI.

The Tigard `0403:6010` is an FT2232H UART/JTAG adapter. It remains useful for
CN16 3.3 V TTL UART, but original-UP2 CN22 is a 1.8 V CPLD/BIOS service header,
not a documented Apollo Lake CPU JTAG chain.

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

1. Genuine Intel SVT DCI DbC2/3 or standards-compliant SuperSpeed debug cable.
2. Exact UP2 board FAB and current firmware identified and recoverable.
3. Firmware DCI/debug consent and `IA32_DEBUG_INTERFACE` enabled and unlocked.
4. Licensed Intel System Debugger/System Bring-Up Toolkit plus supported host.
5. A retained connection receipt proving the target, rather than a USB bridge.
6. A reviewed DCI bootstrap contract or standard UEFI media for actual boot.

