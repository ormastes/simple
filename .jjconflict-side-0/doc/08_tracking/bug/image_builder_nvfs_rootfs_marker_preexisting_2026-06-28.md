# image_builder: nvfs rootfs backend marker assertion fails (pre-existing)

Date: 2026-06-28

## Summary

`test/01_unit/os/installer/image_builder_artifact_spec.spl` block 3 ("writes
rootfs backend markers for alternate hosted backends while keeping FAT32
carrier") fails: the boot marker read back from
`{output}.contents/rootfs/SYS/ROOTFS.CFG` is empty, so `expect(boot_marker).to_contain("rootfs_carrier=fat32")`
fails with an empty actual.

## Pre-existing — NOT caused by the simplebox wiring

Confirmed by running the spec against `origin/main`'s image_builder.spl with the
spec reverted to origin (no `/bin/simplebox` assertions at all): **block 3 still
fails identically** (2 passed / 1 failed). The simplebox/libc wiring landed in
this lane is purely additive (one `write_text` + one manifest line + one payload
helper) and does not touch `_rootfs_boot_marker_payload` or the carrier string.
Block 1 (which now also asserts `/bin/simplebox` is packed) passes.

## Likely cause (unverified)

`_populate_root_partition` writes `SYS/ROOTFS.CFG` from the module-level
`_image_builder_rootfs_backend` global, while `build_install_image_with_rootfs`
takes the backend as a per-call argument. The per-call backend likely is not
threaded into the global before the marker is written (or the with-rootfs build
returns before writing), so the nvfs marker file is empty in block 3.

## Acceptance for closure

- `build_install_image_with_rootfs(..., "nvfs")` writes a non-empty
  `SYS/ROOTFS.CFG` containing `rootfs_carrier=fat32` and `rootfs_backend=nvfs`,
  and block 3 passes — without regressing block 1/2.
