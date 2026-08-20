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
6. Prove halt/resume on a disposable, secret-free target; then prove reset and
   a read of a known non-sensitive physical-memory location. Never unplug DCI
   while the target is halted.

## Boot SimpleOS

The recommended lane is DCI-assisted UEFI boot. Keep the existing removable
GPT/FAT32 image and let UEFI/GRUB establish the boot contract. Use DCI only for
reset, halt, breakpoints, and memory inspection. Accept boot only when CN16 UART
shows the current loader/shim/entry/console/VFS/shell markers and a freshly
injected `ls /` returns `/bin`, `/etc`, and `/README.txt`.

Do not copy `simpleos.elf` to `0x08000000` and set RIP. The current entry is a
32-bit bootstrap contract; arbitrary debugger/UEFI state is incompatible. A
future direct-load lane must supply a reviewed, hash-bound trampoline that
loads all ELF segments, zeroes BSS, reserves valid DRAM, parks other cores, and
constructs exact CPU/register/stack/handoff state.

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

Research and source links are in
`doc/01_research/domain/up_squared_apl_intel_dci_debug.md`.

