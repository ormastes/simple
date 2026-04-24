# TODO: Add mold binary to SimpleOS rootfs at /usr/bin/mold (AC-3 blocker)

**Date:** 2026-04-24
**Feature:** mold-mimalloc-default / AC-3
**Status:** Deferred — no binary-injection mechanism in rootfs build

## What needs to happen

The SimpleOS filesystem image (FAT32 / ext2) should contain the mold ELF
binary at `/usr/bin/mold` so that `mold --help` works inside a QEMU SimpleOS
session.

## Blocker

The current FAT32 image builder (`src/os/qemu_runner.spl`, scenarios
`scenario_x64_nvme_fat32`, `scenario_x64_desktop_disk`) mounts a pre-built
disk image. There is no host→guest binary staging step: no function like
`rootfs_add_binary(host_path, guest_path)` exists in the build pipeline.

`examples/simple_os/arch/x86_64/desktop_e2e_entry.spl` references
`/usr/bin/clang` and `/usr/bin/lld` as smoke-check paths but does not
demonstrate how those binaries were placed into the image.

## What must be built first

1. A `rootfs_inject_binary(img_path: text, host_bin: text, guest_path: text)`
   utility (or equivalent `mcopy`/`e2cp` shell step) in the OS build pipeline.
2. A build-time step that, after `bin/simple build`, copies `bin/mold/mold`
   (downloaded by `scripts/install-mold.shs`) into the FAT32 image at
   `/usr/bin/mold`.

## Files to modify when unblocked

- The FAT32 image construction step (likely in `src/os/qemu_runner.spl` or a
  dedicated `src/os/fs_build.spl` module).
- `examples/simple_os/arch/x86_64/desktop_e2e_entry.spl` — add mold to the
  toolchain-present smoke check alongside clang/lld.
