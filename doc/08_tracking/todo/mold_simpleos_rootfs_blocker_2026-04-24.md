# RESOLVED: Add mold binary to SimpleOS rootfs at /usr/bin/mold (AC-3)

**Date:** 2026-04-24
**Feature:** mold-mimalloc-default / AC-3
**Status:** Resolved — staging-time + post-hoc injection implemented

## Resolution

The injection mechanism already existed: `scripts/make_os_disk.shs` uses
`mcopy -s -i "$OUTPUT" "$TMPDIR"/* ::` (mtools) and `stage_simpleos_toolchain_payloads`
to copy host binaries (clang, lld, rustc, …) into `$TMPDIR/usr/bin/` before
populating the FAT32 image. The missing piece was a mold-specific staging hook.

## Changes made

1. **`scripts/make_os_disk.shs`** — Added `stage_mold_payload()` (modeled on
   `stage_simpleos_toolchain_payloads`). Copies `bin/mold/mold` (or
   `$SIMPLEOS_MOLD_BIN`) to `$TMPDIR/usr/bin/mold` + `$TMPDIR/SYS/APPS/mold`
   + `$TMPDIR/SYS/MOLDMAN.TXT` manifest. Gated on x86_64 arch. Skips
   gracefully when `bin/mold/mold` is absent. Called after toolchain staging.

2. **`src/os/port/rootfs_inject.spl`** — New Simple module with
   `rootfs_inject_binary(image, host_src, guest_dest) -> Result<(), text>` for
   post-hoc mcopy-based injection into an already-built FAT32 image, and
   `rootfs_inject_mold(image, mold_host_path)` convenience wrapper.

3. **`scripts/install-mold.shs`** — Added post-hoc injection block: after
   downloading `bin/mold/mold`, if `build/os/fat32-x86_64.img` exists and
   `mcopy` is available, injects the binary immediately via mcopy. Otherwise
   prints a message that mold will be staged on the next image build.

## How injection works end-to-end

- **New image build:** `sh scripts/make_os_disk.shs` → `stage_mold_payload()`
  copies mold into the staging tmpdir → `mcopy -s` populates the FAT32 image.
- **Existing image:** `sh scripts/install-mold.shs` → mcopy post-hoc injection
  into `build/os/fat32-x86_64.img` if the image exists.
- **From Simple code:** `use os.port.rootfs_inject.{rootfs_inject_mold}` then
  call `rootfs_inject_mold(image_path, "bin/mold/mold")`.

## Note on runtime execution

Mold is a Linux x86_64 ELF. Placing it in the image (matching clang/lld) makes
it present as a fixture; actual execution depends on the SimpleOS userland
environment reaching the level where it can execute host ELFs.
