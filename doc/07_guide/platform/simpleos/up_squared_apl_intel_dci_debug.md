# UP Squared Apollo Lake Intel DCI programming and debug guide

## Supported meaning

Original Apollo Lake UP Squared can conditionally use Intel DCI USB 3.x Debug
Class for JTAG-like run control and physical-memory access. This requires a
qualified SuperSpeed DbC cable, firmware debug consent, an enabled/unlocked
debug interface, and Intel System Debugger/System Bring-Up Toolkit. Smart KM
Link, ordinary A-to-A USB, Tigard, CN22, GDB, and OpenOCD are not substitutes.

Start with the read-only inventory:

```sh
scripts/check/check-up-squared-apl-dci.shs --inventory
```

`blocked` is expected until a retained Intel-tool connection receipt exists.
Never infer readiness from a connector or unknown USB VID/PID.

## Current host checkpoint (2026-08-21)

The host is Ubuntu 24.04.4. No Intel System Debugger/System Bring-Up Toolkit
installer, installation directory, or `/etc/udev/rules.d/99-dci.rules` is
present. Intel does not publish this toolkit through Ubuntu APT: installation
starts only after the operator completes Intel's corporate-NDA request and
downloads the authenticated Registration Center package. Do not use a mirror,
guess a package name, or install a similarly named debugger.

The observed Smart KM Link `0ea0:2211` is a USB 2.0 mass-storage/HID composite
at 480 Mbit/s, not a DCI target endpoint. A passive cable may not enumerate by
itself, so the decisive test remains Target Connection Agent discovering the
Apollo Lake target and CPU threads. The Intel request page and the UP community
DCI discussion were opened for the operator; BIOS enablement is still
unproven until the exact board menu or a successful target receipt confirms it.

## Safe enablement sequence

1. Record exact `UPS-APL` model, board FAB, BIOS version, RAM, and storage.
2. Back up firmware with a verified external recovery path before considering
   any firmware change. Do not use the old FAB-A debug image by default.
3. Install the licensed Intel toolkit on a supported host and its DCI udev
   rules. Use a genuine Intel SVT DCI DbC2/3 or qualified SuperSpeed debug cable.
4. In the board's existing BIOS, inspect only the board-specific DCI/debug
   consent settings. Menu names vary. Do not patch `IA32_DEBUG_INTERFACE` or
   flash firmware as part of this guide.
5. Connect through Target Connection Agent and retain a receipt identifying
   target, connection type, tool version, cable, firmware, and timestamp.
6. Prove halt/resume on a disposable, secret-free target, then read a known
   non-sensitive physical-memory location. Never unplug DCI while halted.

Do **not** use OpenRC warm reset on Apollo Lake. Intel documents that it can
leave cores unreleasable in an undefined state and gives manual reset as the
recovery. Treat physical reset as the baseline. A toolkit Power-Good reset is a
separate experiment and is accepted only after exact-board evidence.

## Boot SimpleOS

The selected scope is A+B+D: DCI-assisted UEFI first boot, a UEFI-resident RAM
mailbox loader for repeated boots, and a target-side storage provisioner. Raw
debugger-authored CPU-state boot and open xHCI DbC are excluded from this work.

The recommended lane is DCI-assisted UEFI boot. Keep the existing removable
GPT/FAT32 image and let UEFI/GRUB establish the boot contract. Use DCI only for
reset, halt, breakpoints, and memory inspection. Accept boot only when CN16 UART
shows the current loader/shim/entry/console/VFS/shell markers and a freshly
injected `ls /` returns `/bin`, `/etc`, and `/README.txt`.

Do not copy `simpleos.elf` to `0x08000000` and set RIP. Its three `PT_LOAD`
segments use different file offsets/physical addresses, and the writable
segment expands from 138 file bytes to `0x0180d000` memory bytes. The current
entry is a 32-bit bootstrap contract; arbitrary debugger/UEFI state is
incompatible.

The preferred direct-memory design is a resident UEFI loader: it allocates and
publishes a staging mailbox, DCI writes the hash-bound image, and target code
parses ELF, zeros BSS, exits firmware, parks cores, and constructs exact
Multiboot state. Raw debugger-controlled register/CR/GDT/page-table setup is a
last-resort design, not an operational command in this guide.

## Read and write storage

DCI may stage an image in RAM but does not write blocks. Use one of:

- the existing identity-gated removable-media writer on the writer host; or
- a trusted RAM/PXE Linux/provisioner on UP2 with a real device driver.

Before any write, bind model, serial, transport, capacity, partition layout,
mount/holder state, and root/swap exclusion. Write only explicit bounds, flush,
then hash the exact-length readback. Never program eMMC/SATA/USB controller MMIO
through debugger memory writes. Never treat the M.2 E-key as generic NVMe.

## Open alternative

SimpleOS may later implement xHCI DbC as a high-speed post-entry console/GDB
remote endpoint. It uses similar cabling but is not Intel DCI and cannot provide
pre-boot reset/halt/memory load before target software initializes xHCI.

## Free first-light and software-debug path

The free path does not emulate Intel DCI. It boots the existing removable UEFI
image, observes CN16, and exposes a bounded target-resident GDB RSP memory
monitor after SimpleOS starts. Use this exact CN16 UART wiring:

| CN16 pin | UP2 signal | Connect to Tigard Port A |
|---:|---|---|
| 8 | GND | GND |
| 9 | UART RX, 3.3-V TTL | TX (only when input is needed) |
| 10 | UART TX, 3.3-V TTL | RX |

Never connect CN16 pins 1 or 5 (5 V). Configure 115200 8N1, no flow control.
Tigard interface 00 is Port A/Serial; interface 01 is Port B/JTAG. Do not send
UART data through the JTAG interface and do not connect 3.3-V Tigard JTAG to the
1.8-V CN22 CPLD/BIOS header.

SimpleOS initializes COM1 before its first `UP2 entry` marker. Its loopback
self-test must consume the injected `0xAE` byte before the shell starts; a raw
transcript containing `ae 6c 73 20 2f` identifies a stale probe byte. The
admitted OVMF check covers this invariant.

On the host:

```sh
picocom --baud 115200 --flow none --databits 8 --parity n --stopbits 1 \
  /dev/serial/by-id/usb-Tigard_port_A:Serial_port_B:JTAG_*-if00-port0
```

Insert the admitted UEFI USB image, use F7 for the one-time UEFI boot menu, and
capture from power-on/reset through the fresh `ls /` response. A quiet UART is
not PASS: verify power, pin 10-to-RX and pin 8-to-GND first, then capture factory
firmware output to separate wiring from a SimpleOS UART-routing problem.

### Load and verify staging RAM with GDB

At the SimpleOS prompt, type `gdb`. The monitor then owns the serial port until
detach. Exit picocom without resetting the board, and attach host GDB to the
same stable serial path:

```gdb
set serial baud 115200
set remotetimeout 5
target remote /dev/serial/by-id/usb-Tigard_port_A:Serial_port_B:JTAG_*-if00-port0
maintenance packet M0a000000,4:53494d50
maintenance packet m0a000000,4
detach
```

The read response must be `53494d50`. Valid addresses are exactly
`0x0a000000..0x0b000000`, with at most 1024 bytes per packet. The writable ELF
`PT_LOAD` reserves this 16 MiB staging range, and every `M` packet is read back
before `OK`. Use `maintenance packet` for this current memory-only monitor;
ordinary register display, breakpoints, `continue`, `step`, reset, and binary
`X` packets are not implemented and return unsupported. This is post-boot RAM
access, not preboot DCI/JTAG or a direct CPU-state boot method.

The canonical OVMF checker proves the sequence `qSupported` → write `SIMP` →
read `53494d50` → detach while retaining the earlier boot/VFS/`ls /` evidence.
Physical CN16 PASS still requires the exact board transcript.

Do not install CHIPSEC on the host expecting remote access. CHIPSEC must execute
on UP2 under a trusted Linux/Windows driver or UEFI agent. Linux xHCI DbC and the
SimpleOS GDB monitor are post-initialization software tools; neither can
halt or reset an otherwise dead target.

Research and source links are in
`doc/01_research/domain/up_squared_apl_intel_dci_debug.md`.
