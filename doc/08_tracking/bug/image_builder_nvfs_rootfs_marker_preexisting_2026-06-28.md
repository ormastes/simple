# image_builder: nvfs rootfs backend marker assertion fails (pre-existing)
## Repair candidate 2026-11-03 — behavioral verification blocked

Current source already assigns the per-call backend before constructing the
image. The remaining source failure boundary is unchecked metadata writes:
`_populate_root_partition` ignored both write statuses and advertised the files
in its manifest even when staging failed. `image_rootfs_markers.spl` now checks
directory creation, both writes, and actual readback against the selected
backend. The builder captures that backend for the build and validates again
after package/installer population, before publishing manifests or the image.
Existing stale marker files are replaced; missing, empty, malformed or wrong
backend metadata fails validation.

`image_rootfs_markers_spec.spl` authors seven real temporary staged-image cases:
fresh nvfs, preexisting dbfs replacement, missing boot marker, malformed/empty
boot marker, a file blocking `SYS`, malformed rootfs configuration, and a
directory blocking the marker file write. The
original artifact spec now uses `MIN_IMAGE_SIZE_MB_V1` instead of the obsolete
64 MB size that fails before marker staging under today's 67 MB minimum.

**TEST_BLOCKED:** no qualified self-hosted CLI is available on this host.
Authored cases are not passing execution evidence (executed test count: 0).
Run both marker and artifact specs with an admitted producer before closure.

## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Triage note 2026-09-13 — left OPEN: needs a SimpleOS build/QEMU lane unavailable here
- **measured**: the referenced product paths still exist, so there is no removed-code basis for a stale closure.
- **inferred**: reproduction needs the SimpleOS x86_64 build artifacts / QEMU system-test lane (and for the SSP item, a clang hardening-flag build). This triage host is Windows with no such lane, and `bin/simple test` is broken here regardless.
- **inferred**: no work attempted — the changes would land in `src/compiler/**` or `src/app/compile/**`, and a bootstrap is running concurrently in this workspace.

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


## Triage 2026-11-04 (lane g-image-builder-nvfs, Windows seed host)

- RED on origin/release/1.0.0 (`bin/simple.exe test image_builder_artifact_spec.spl`):
  3 executed, 1 passed, 2 failed. The "3 undefined symbols" from the 2026-09-19
  note no longer exist: every `use` in `image_builder.spl` resolves and
  `build_install_image_with_rootfs` runs.
- The marker defect itself is fixed: a 512 MB nvfs build stages
  `SYS/ROOTFS.CFG` = `rootfs_backend=nvfs / rootfs_carrier=fat32 / rootfs_boot_mode=fat32-carrier`.
- Remaining reds, both outside the marker code:
  1. `MIN_IMAGE_SIZE_MB_V1 = 67` with `EFI_PARTITION_SIZE_MB = 64` leaves a root
     partition of about 2 MB, below `_IMAGE_ROOTFS_METADATA_MIN_BYTES_V1` (4 MiB), so
     `_validate_staged_rootfs_budget_v1` returns "metadata reserve exceeds root
     partition capacity" for the spec's size. The minimum must be derived from the
     EFI size + 4 MiB reserve + the font bundle (needs a measured staged size, not a guess).
  2. FAT32 generation (`refusing non-bootable descriptor fallback`) and the spec's
     `/bin/sh` `_reset_dir` need a Linux host; unverifiable on this Windows seed.
- No source change made: choosing the new minimum needs a measured staged-size budget on Linux.

## Update 2026-11-06 (work/fx-os-kernel-20261106)

Verdict: SPEC DRIFT, not a marker regression. `image_rootfs_markers_spec` passes
7/7. Block 3 of `image_builder_artifact_spec` failed because
`build_install_image_with_rootfs` returned `Err("SimpleOS staged rootfs metadata
reserve exceeds root partition capacity")` (`src/os/installer/image_builder.spl:1991`):
at `MIN_IMAGE_SIZE_MB_V1` = 67 MB `_compute_layout` leaves a 1 MB root partition,
below the 4 MB `_IMAGE_ROOTFS_METADATA_MIN_BYTES_V1`, and the staged rootfs now
carries ~50 MB of fonts under `SYS/FONTS`. The budget guard is correct; the spec
now builds with a 128 MB image (`_FULL_ROOTFS_IMAGE_MB`); assertions unchanged.
Block 3 passes: artifact spec 1/3 -> 2/3. Remaining failure ("writes
installer-media staging for non-x86 architectures", arm64 ISO) builds Ok at 128 MB
but one output/contents-path expectation is false; separate, still open.

## Update 2026-11-10 (work/g100-os_boot)

The manual-scenario addition in `f10491812210` introduced a fourth artifact
scenario using a 64 MB image. Current `ImageBuilder.build` rejects every size
below `MIN_IMAGE_SIZE_MB_V1` (67 MB) before staging; the scenario therefore
cannot reach any of its filesystem assertions. Its fixture now uses the same
128 MB `_FULL_ROOTFS_IMAGE_MB` as the existing full-rootfs scenarios. The
original nvfs marker assertions and every executable-presence assertion are
unchanged.

This is a fixture prerequisite correction, not image-builder qualification.
The artifact spec and marker spec were not executed in this lane: no admitted
self-hosted test runner was available, and FAT32 image generation requires the
Linux tooling used by the builder. The record remains unresolved, with
verification pending on those runs and changed-spec manual generation.

The remaining artifact expectations also need a controlled native-payload
fixture. The ARM64 installer scenario supplies no installer bytes while
`_populate_install_media` deliberately records a blocked executable payload.
The disk scenario similarly expects `/sbin/init` despite an explicit empty
candidate; its toolchain executable paths can additionally depend on ambient
native-tool discovery. Do not restore fabricated executables or flip all those
assertions without testing the applicable payload contract.
