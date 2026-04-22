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
Native build reaches the freestanding unresolved-symbol guard and reports
hundreds of unexpected symbols. A resolver follow-up reduced the import warning
surface, but the guard still rejects the build without
`SIMPLE_ALLOW_FREESTANDING_STUBS=1`.

Observed command:

```sh
SIMPLE_TEST_DISABLE_CACHE=1 SIMPLEOS_QEMU_DESKTOP_DISK_LIVE=1 bin/simple test test/system/simpleos_desktop_disk_boot_spec.spl
```

Failure class:

- `Freestanding unresolved symbol check: 714 unexpected symbol(s)`
- remaining warnings include unresolved `std`, `os.path`, and similar package
  aliases from the HIR imported-type preload path
- test duration remains over 100 seconds and the runner marks it `[PERF BUG]`

This should be fixed in the native-build entry-closure/import-resolution lane
before treating desktop save/readback as a VFS regression.

## Diagnostic x86_64 Boot With Freestanding Stubs Allowed

For diagnosis only, the build was run with:

```sh
SIMPLE_BOOTSTRAP=1 SIMPLE_ALLOW_FREESTANDING_STUBS=1 SIMPLE_LIB="$(pwd)/src" \
  PATH="/usr/bin:$PATH" src/compiler_rust/target/debug/simple native-build \
  --source src/os --source src/lib --source examples/simple_os \
  --backend cranelift --entry-closure \
  --entry examples/simple_os/arch/x86_64/desktop_e2e_entry.spl \
  --target x86_64-unknown-none \
  -o build/os/simpleos_desktop_e2e_32.elf \
  --linker-script examples/simple_os/arch/x86_64/linker.ld
```

That diagnostic ELF boots under the NVMe desktop disk shape and reaches:

- `[vfs-init] Found NVMe device at index 3`
- `[vfs-init] C NVMe controller initialized!`
- `[vfs-init] executable load probe ok path=/sys/apps/browser_demo ...`
- `[vfs] mounted fat32 device=nvme0 volume=simpleos`
- `[desktop-e2e] launcher-ready apps=5`
- `[launcher] posix_spawn begin name=Browser Demo path=/sys/apps/browser_demo.smf`
- `[exec-source] resolve initramfs returned path=/sys/apps/browser_demo`

It then faults before logging `vfs_alias_hit` or `vfs_miss`. This means the x86
storage and launcher setup reaches the executable-source boundary, but the
diagnostic run is still contaminated by weak freestanding stubs and is not a
production PASS.

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
