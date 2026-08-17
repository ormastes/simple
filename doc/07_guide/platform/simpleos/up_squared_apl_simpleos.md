# UP Squared Apollo Lake (N4200 / N3350) SimpleOS bring-up

## Purpose

Run a SimpleOS UEFI image from removable media on an original UP Squared Apollo Lake
board and prove real VFS-backed boot+`ls /` over serial in a single transcript.

## Current scope

- Target: `x86_64-up-squared-apollo-lake`
- Board boot path: removable USB GPT/FAT32, `EFI/BOOT/BOOTX64.EFI`, BIOS **F7** boot menu
- Acceptance oracle: `scripts/check/check-simpleos-up-squared-apollo-lake.shs`
- Default live capture: serial markers plus correlated `ls` markers

## Hardware / safety guardrails

- CN16 debug UART is 3.3 V TTL. CN22 is a CPLD/BIOS-update connector, not a CPU JTAG
  path for SimpleOS work.
- Use the removable USB stick physically on the writer host for `dd`/readback; board-attached
  OTG is not an admitted remote block writer path.
- Never write UP2 internal eMMC/NVMe, BIOS SPI, or mounted system disks.
- On first-light, do not use destructive network/PXE fallback if removable media path is available.

If you cannot keep the USB stick on the writer host, only continue with board-side
admission after UP2 has already booted a trusted Linux environment (normal boot or
PXE RAM Linux):

- copy `board-usb.img` to UP2, hash and confirm,
- identify the target with one stable `/dev/disk/by-id` plus serial/capacity,
- reject root/swap/mounted/internal media before any write,
- write locally on UP2, sync, rerun identity readback, and verify exact image-length hash.
- return to UEFI boot and boot from USB only after the write is confirmed.

## Build and image

1. Build ELF and image:

```sh
sh scripts/os/build-simpleos-up-squared-apollo-lake.shs
sh scripts/os/build-simpleos-x86_64-board-usb.shs
```

Artifacts:

- `build/os/up-squared-apollo-lake/simpleos.elf`
- `build/os/up-squared-apollo-lake/usb/board-usb.img`
- `build/os/up-squared-apollo-lake/simpleos.elf.receipt`

2. Pre-flight contract checks:

```sh
sh scripts/check/check-simpleos-up-squared-apollo-lake.shs --contract
```

3. Admit the target device on writer host:

```sh
UP2_USB_IMAGE=build/os/up-squared-apollo-lake/usb/board-usb.img \
  sh scripts/os/write-simpleos-up-squared-usb.shs --mode dry-run --by-id <id>
```

Re-run with `--mode write --allow-destructive --confirm <token>` after identity confirmation.

The admission script verifies by-id, model/serial/capacity, removable flag, non-root/swap
status, unmounted/holder-free state, full-image write, and exact-length SHA-256 readback.

## Board boot and verification

1. Insert the stick into UP2 (USB Type-A host port), choose USB in one-time F7 menu.
2. Capture boot transcript while the board runs SimpleOS.
3. Run live checker (stateful transcript preferred):

```sh
UP2_UART_PATH=/dev/ttyUSB0 \
UP2_UART_LOG=/path/to/recorded.uart.log \
  sh scripts/check/check-simpleos-up-squared-apollo-lake.shs --live
```

Success requires ordered markers and correlated root listing:

- `UP2 entry`
- `UP2 console-ready`
- `UP2 filesystem-ready entries=...`
- `UP2 shell-ready`
- `UP2 ls-begin source=vfs command=ls /`
- `UP2 ls-end status=pass`
- `/bin`, `/etc`, `/README.txt` between begin/end

## Known blocked states

- No removable USB present on writer host: `--live` cannot proceed.
- Missing serial path / silent reader: `up2_status=blocked` or `fail`.
- Offline image pass is not physical PASS; only live transcript can satisfy board acceptance.
