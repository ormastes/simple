# Baremetal arm32: AAVMF32 does not load the ESP (2026-11-17)

- id: `baremetal_arm32_aavmf32_no_esp_boot_2026_11_17`
- severity: P3
- status: root-caused (verification-pending)

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

## Root cause (2026-11-17, WSL Ubuntu-24.04, qemu-system-arm 8.2.2)
The ESP was found. The image was rejected: `BdsDxe: failed to load Boot0001 ...: Unsupported`.
`lld-link -machine:arm` writes PE Machine `0x01c4` (ARMNT), but EDK2 ARM accepts only
`0x01c2` (ARMTHUMB_MIXED). Patching the two bytes at `e_lfanew+4` to `c2 01` makes
AAVMF32 start the app (`BdsDxe: starting Boot0001`, test app printed over ConOut) from
a `mkfs.vfat` superfloppy image on `-device virtio-blk-pci`. The same unpatched image failed
on virtio-blk-pci (legacy and modern), nvme, usb-storage and virtio-scsi, so the bus was
never the problem. Real-firmware path, no U-Boot, no `-kernel`.
Not yet verified: QEMU vvfat (`fat:rw:`) with the patched image.
Next: patch Machine to `0x01c2` in the arm32 EFI image build; add the `arm32` case to
`check-baremetal-efi-boot.shs`. Firmware provisioning: `scripts/setup/provision-xc-firmware.shs`.
