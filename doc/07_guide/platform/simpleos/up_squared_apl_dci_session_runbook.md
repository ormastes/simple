# UP Squared Apollo Lake DCI session runbook

This runbook records the steps that are public and safe. Intel's exact System
Debug command/API documentation is NDA-controlled and bundled with the
CNDA-controlled toolkit; do not invent commands from another debugger.

## 1. Identify before connecting

Record original-board part number, FAB, CPU SKU, RAM, BIOS vendor/version, and
all storage model/serial/capacity values. Remove secrets. Confirm an external
SPI recovery path before any separately authorized firmware work.

Use an Intel SVT DCI DbC2/3 cable/probe or another cable explicitly qualified
by Intel's target-connection documentation. Intel describes USB 3.x DCI as the
target acting in the DFP/host role; original UP2 Type-A ports are host ports.
The Micro-B OTG port is not assumed to be the DCI port. Determine the exact port
through Target Connection Agent and board/tool documentation, not trial writes.

## 2. Connect without mutation

Launch `<install-dir>/iss_ide_eclipse-launcher.sh`. In Target Connection Agent,
create a connection for the exact Apollo Lake target and select USB 3.x Debug
Class. A USB enumeration or “connected” badge alone is insufficient: enumerate
the expected CPU threads and retain target/tool/cable/firmware identity.

Create `up2-dci-connection-v1` evidence with:

```text
schema=up2-dci-connection-v1
status=pass
target=original-up-squared-apollo-lake
connection=usb3-dbc
debug_interface=enabled-unlocked
reset_policy=hardware-baseline-openrc-warm-reset-forbidden
board_fab=...
bios_version=...
tool_version=...
cable_identity=...
timestamp_utc=...
```

Pass it to the local read-only gate:

```sh
UP2_DCI_CONNECTION_RECEIPT=/absolute/path/to/receipt \
  scripts/check/check-up-squared-apl-dci.shs --inventory
```

## 3. Qualify run control and memory

With no storage mutation configured, halt and resume once while CN16 UART is
captured. Read a known public firmware code/data location and compare it with an
independent firmware map or debugger symbol. Do not use an unverified address,
write memory, or disconnect the cable while halted.

OpenRC warm reset is forbidden on Apollo Lake because Intel documents a stranded
core failure with no software workaround. Use physical reset for recovery. A
Power-Good reset is an unqualified optional experiment until proven on this FAB.

## 4. Load and boot software

Preferred first boot: let UEFI/GRUB load the existing removable image while DCI
provides breakpoints and inspection. Loading symbols into the debugger does not
load executable bytes into target RAM.

Preferred repeated RAM boot: first boot a reviewed resident UEFI loader. It
allocates a staging buffer and publishes address, size, generation, and nonce.
Write payload bytes first, then a descriptor containing exact length and SHA-256
last. Resume target code; it validates the descriptor, parses every `PT_LOAD`,
zeros `p_memsz - p_filesz`, obtains the current memory map, exits boot services,
constructs Multiboot state, and transfers through the existing 32-bit shim.
This loader is **not implemented yet**. `dci_mailbox.spl` validates policy only;
do not treat its tests or the post-boot RSP staging area as a boot loader. UEFI's
Debug Support Table may help an external debugger find loaded images when
firmware publishes it, but it does not supply the missing loader.

Inspect the exact current ELF/receipt and obtain its segment manifest without
touching hardware:

```sh
scripts/check/inspect-up-squared-apl-dci-elf.shs --inspect
```

Do not directly set RIP to `0x08000038`. Do not use debugger register writes to
guess CR0/CR3/CR4/EFER, GDT, paging, stack, AP state, or firmware ownership.

## 5. Read/write storage

DCI physical-memory DMA is only transport into RAM. A resident provisioner must
use a real target-side NVMe/eMMC/SATA/USB driver. Before write, display and confirm
model, serial, transport, capacity, partition table, root/swap, mounts, holders,
and byte bounds. Write, flush, re-enumerate, and hash exact readback. Never use
debugger MMIO writes to operate a storage controller.

The free SimpleOS NVMe path is executable for a controller that really
enumerates as PCI class `01:08`. Run `nvme identify`, verify its PCI
identity, model, serial, firmware, NSID, LBA size/count, and capacity, then enter
only the exact printed `nvme format FORMAT:...` command. Successful output must
report GPT/FAT32, flush, fresh-adapter readback, and `/nvme/proof.txt` from
`ls /nvme`. The original board has no native M-key slot; an adapter is accepted
only after live PCI class `01:08` and NVMe Identify, never by connector shape.

Boot PASS still requires a fresh CN16 transcript through VFS-backed `ls /`.
Storage PASS additionally requires the identity and readback receipt. A DCI
connection, memory read, or debugger screenshot cannot substitute for either.

## 6. Free fallback when Intel DCI is unavailable

Install/use GNU GDB, OpenOCD, and picocom. Before opening a debug session,
qualify the cable with `lsusb -v`: a usable Tigard must enumerate as FTDI
`0403:6010`; CN16 UART must create a tty device; a DCI/DbC path must enumerate
through the intended USB3 debug interface. A Smart KM Link `0ea0:2211` with
mass-storage plus HID keyboard/mouse interfaces is not a UART, Tigard, or DCI
cable. `openocd -f interface/ftdi/tigard.cfg -c init -c shutdown` returning
`no device found` is a physical-transport BLOCKED result; do not retry it as a
reset loop.

Use CN16 pins 8/9/10 (GND/board-RX/board-TX), 3.3-V TTL, 115200 8N1, no flow
control. Adapter RX connects to board pin 10; adapter TX connects to board pin
9; adapter ground connects to pin 8. Never connect adapter VCC or CN16 5-V pins
1/5. CN22 pin 4 is 1.8 V and its documented JTAG is FPGA service, not a CPU
debug port; its full electrical thresholds are unpublished. Record Secure Boot
state, use F7 for the one-time boot entry (DEL or ESC for setup), and retain the
entire UART transcript. An EFI-shell launch is a separately recorded fallback.

The current tree contains a bounded memory-only GDB RSP monitor: enter `gdb`,
then use checksummed `M`/`m` packets only within
`0x0a000000..0x0b000000`; detach returns to the shell. Registers, breakpoints,
continue, step, reset, and binary `X` remain unsupported. The tree still lacks
an xHCI DbC transport. Host KGDB, CHIPSEC, and EDK II debug agents become useful
only after corresponding target software starts. Record such evidence as
software-debug, not DCI run-control or external-memory evidence.
