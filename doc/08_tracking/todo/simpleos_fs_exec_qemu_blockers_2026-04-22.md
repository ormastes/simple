# SimpleOS FS Exec QEMU Blockers (2026-04-22)

## Context

Feature lane: filesystem app load/execution from shell app to WM GUI app.

The VFS exec path now maps canonical launcher SMF paths such as
`/sys/apps/browser_demo.smf` to the FAT32 8.3 filenames seeded on the boot
images, such as `/SYS/APPS/BROWSMF.SMF`. Focused VFS/launcher specs pass, and
the x86_64, arm64, and arm32 FAT32 images rebuild with app payloads present.

## Fresh Verification Commands

```sh
sh scripts/make_os_disk.shs 64 build/os/fat32-x86_64.img "" x86_64
sh scripts/make_os_disk.shs 64 build/os/fat32-arm64.img "" arm64
sh scripts/make_os_disk.shs 64 build/os/fat32-arm32.img "" arm32
SIMPLE_TEST_DISABLE_CACHE=1 SIMPLEOS_QEMU_DESKTOP_DISK_LIVE=1 bin/simple test test/system/simpleos_desktop_disk_boot_spec.spl
bin/simple os test --scenario arm64-virtio-fat32-smf
bin/simple os test --scenario arm32-virtio-fat32-smf
```

## Blocker: x86_64 Desktop Disk Live Lane

The desktop disk spec fails before QEMU can exercise editor save/readback.
Native build reaches the freestanding unresolved-symbol guard and reports 455
unexpected symbols after repeated `cannot resolve import: module path segment
os not found` warnings.

Observed command:

```sh
SIMPLE_TEST_DISABLE_CACHE=1 SIMPLEOS_QEMU_DESKTOP_DISK_LIVE=1 bin/simple test test/system/simpleos_desktop_disk_boot_spec.spl
```

Failure class:

- `Freestanding unresolved symbol check: 455 unexpected symbol(s)`
- import resolver searches under paths such as `examples/simple_os/arch/x86_64/os`
  and `src/os/kernel/ipc/os`
- test duration was about 103 seconds and the runner marked it `[PERF BUG]`

This should be fixed in the native-build entry-closure/import-resolution lane
before treating desktop save/readback as a VFS regression.

## Blocker: ARM64 VirtIO-BLK FAT32 SMF Lane

The ARM64 image builds and QEMU boots, but FAT32 mount never reaches BPB
parsing because the first VirtIO-BLK read times out.

Observed command:

```sh
bin/simple os test --scenario arm64-virtio-fat32-smf
```

Failure signature:

- `[virtio-blk] direct read timeout lba=0`
- `[virtio-blk] read DMA allocation failed bytes=529`
- `[vfs-root] direct_sector_failed lba=0`
- `[vfs-init] FAT32 BPB probe failed`
- `[arm-fs-exec] vfs:fail`

This is below VFS path aliasing; the block device cannot deliver sector 0.

## Blocker: ARM32 VirtIO-BLK FAT32 SMF Lane

The ARM32 image builds and QEMU boots, then the VirtIO queue state becomes
invalid before the scenario can report `TEST PASSED`.

Observed command:

```sh
bin/simple os test --scenario arm32-virtio-fat32-smf
```

Failure signature:

- `qemu-system-arm: Guest says index 65535 is available`

Investigate VirtIO queue initialization, available-ring index writes, and any
32-bit pointer/address truncation in the ARM32 VirtIO-BLK path.
