# UP Squared Apollo Lake DCI session runbook

This runbook records the steps that are public and safe. Intel's exact System
Debug command/API documentation is NDA-controlled and bundled with the licensed
toolkit; do not invent commands from another debugger.

## 1. Identify before connecting

Record original-board part number, FAB, CPU SKU, RAM, BIOS vendor/version, and
all storage model/serial/capacity values. Remove secrets. Confirm an external
SPI recovery path before any separately authorized firmware work.

Use an Intel SVT DCI DbC2/3 qualified cable. Intel describes USB 3.x DCI as the
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

Inspect the exact current ELF/receipt and obtain its segment manifest without
touching hardware:

```sh
scripts/check/inspect-up-squared-apl-dci-elf.shs --inspect
```

Do not directly set RIP to `0x08000038`. Do not use debugger register writes to
guess CR0/CR3/CR4/EFER, GDT, paging, stack, AP state, or firmware ownership.

## 5. Read/write storage

DCI physical-memory DMA is only transport into RAM. A resident provisioner must
use a real target-side eMMC/SATA/USB driver. Before write, display and confirm
model, serial, transport, capacity, partition table, root/swap, mounts, holders,
and byte bounds. Write, flush, re-enumerate, and hash exact readback. Never use
debugger MMIO writes to operate a storage controller.

Boot PASS still requires a fresh CN16 transcript through VFS-backed `ls /`.
Storage PASS additionally requires the identity and readback receipt. A DCI
connection, memory read, or debugger screenshot cannot substitute for either.
