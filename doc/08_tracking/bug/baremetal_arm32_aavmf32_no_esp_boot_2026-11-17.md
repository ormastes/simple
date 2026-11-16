# Baremetal arm32: AAVMF32 does not load the ESP (2026-11-17)

- id: `baremetal_arm32_aavmf32_no_esp_boot_2026_11_17`
- severity: P3
- status: open (blocker filed)

## What works
`native-build examples/09_embedded/freestanding_hello/main.spl --target armv7-unknown-none`
and `--target arm-unknown-none` each exit 0 (1784-byte objects, phase-2 compiler,
WSL Ubuntu-24.04).

## Blocker (precise)
`/usr/share/AAVMF/AAVMF32_CODE.fd` is present. Under `qemu-system-arm -machine
virt`, though, it does not load `EFI/BOOT/BOOTARM.EFI` from the
`-drive file=fat:rw:<esp>` ESP. That is the same pattern that works for
AAVMF (aarch64) in `check-baremetal-efi-boot.shs`. So no real-firmware path
reaches the image. The check also has no `arm32` case, and there is no
`crt0_arm32.S` (a PL011 at 0x09000000, `ldrb`/`strb`, `wfi`).

## Next step
Find out why AAVMF32 does not use the virtual FAT drive. Try `virtio-blk-device`
with a real FAT image made by `mkfs.vfat`/`mtools`, not QEMU vvfat. Or use
U-Boot `qemu_arm_defconfig` (built with clang) as the firmware, with a `bootefi`
or `go` payload. Never `-kernel`.
