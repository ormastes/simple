# SimpleOS on original UP Squared Apollo Lake

## Scope

This lane targets the original UPS-APL board (N4200/N3350), not UP Squared Pro,
V2, 6000, or later boards. It boots a removable x86-64 UEFI image and must prove
the real VFS-backed `ls /` path over the 3.3 V TTL console.

## Build and package

Use an admitted self-hosted compiler with adjacent provenance:

```sh
SIMPLE_BUILD_COMPILER=/path/to/admitted/stage3/simple \
  sh scripts/os/build-simpleos-up-squared-apollo-lake.shs
sh scripts/os/build-simpleos-up-squared-usb-image.shs
```

The kernel build binds the canonical `simple-core` runtime capsule, native x86
runtime members, Multiboot CRT, and the UP2 serial-input provider. The packaged
disk is GPT with one FAT32 ESP and `EFI/BOOT/BOOTX64.EFI`. The ELF64 removable
lane uses Multiboot2; the image checker requires the embedded command plus
`UP2 loader-ready` and `UP2 kernel-admitted` serial markers.

Current OVMF evidence reaches the loader, 32-bit shim, 64-bit bootstrap, board
entry, console, filesystem, and shell. A freshly injected `ls /` returns
`/bin`, `/etc`, and `/README.txt` through the public VFS. This closes the prior
emulated transition blocker; it still does not prove a physical UP2 boot.

## Media safety and boot

The USB stick must be attached to the computer that writes it. A stick inserted
in UP2 is not remotely visible to this workstation merely because UART is
connected. If UP2 already runs trusted Linux over SSH or a RAM/PXE environment,
copy and hash the image there, then admit one stable `/dev/disk/by-id` identity,
serial, capacity, removable flag, mount/holder state, and root/swap exclusion.
Otherwise move the stick to the writer host. Admit it without writing first:

```sh
scripts/os/write-simpleos-up-squared-usb.shs \
  --device-by-id /dev/disk/by-id/usb-EXACT_ID \
  --expected-serial EXACT_SERIAL
```

Verify the printed model, serial, capacity, and image hash. Only then rerun as
root with `--write-media --confirmation EXACT_SHA256`; retain the emitted media
receipt. The confirmation is bound to the exact device identity and image.

Never execute a generic `dd ... /dev/sdX` example. Never write UP2 eMMC/SATA,
BIOS/SPI, UEFI variables, or CN22. After an admitted full-image write, read back
exactly the image length and require SHA-256 equality. Insert the stick in a
Type-A host port, use a USB keyboard to select the one-time F7 UEFI entry, and
leave internal storage unchanged.

## Live evidence

CN16 UART is 3.3 V TTL at 115200 8N1 with no flow control. CN22 is for CPLD/BIOS
service, not Apollo Lake CPU JTAG. Physical PASS requires one retained session
with ordered `UP2 entry`, `console-ready`, `filesystem-ready`, and `shell-ready`
markers followed by a command-correlated `ls /` response containing `/bin`,
`/etc`, and `/README.txt` from the public VFS path. A structurally valid image or
historical transcript does not prove the current board boot.

Apollo Lake may instead expose proprietary Intel DCI through a qualified USB
3.x DbC cable when firmware and architectural debug gates permit it. This is
not CN22, Tigard, Smart KM Link, or generic OpenOCD. See
`up_squared_apl_intel_dci_debug.md` for the fail-closed debug boundary.

Run the physical oracle with the retained media receipt:

```sh
UP2_MEDIA_RECEIPT=/absolute/path/to/media.receipt \
  scripts/check/check-simpleos-up-squared-apollo-lake.shs --live
```
