# NFR options: SimpleOS on UP Squared Apollo Lake

Status: pending user selection

## NFR set A — Fail-closed physical evidence (recommended)

- Stable USB/Tigard identity; never depend on transient `/dev/ttyUSB*` or
  `/dev/sdX` numbering.
- Image writes require an explicit removable `/dev/disk/by-id` target, exact
  serial confirmation, no mounts/holders, non-system-disk proof, and full
  image-length SHA-256 readback.
- Persistent writes are limited to the selected removable USB. No eMMC,
  SATA/NVMe, SPI/BIOS, UEFI-variable, or CN22 JTAG writes.
- One bounded live session proves ordered UEFI/entry/console/filesystem/shell
  markers and command-correlated `ls /` output sourced from VFS.
- Missing hardware is BLOCKED; malformed evidence, wrong media, unsafe target,
  boot crash, or fake/static listing is FAIL.
- Effort: medium.

## NFR set B — Fast lab iteration

- Permit device-node selection and skip full media readback after the first
  write; accept boot-time root-entry markers without command correlation.
- Pros: faster iteration and simpler scripts.
- Cons: identity races can overwrite the wrong disk; evidence can falsely pass
  without executing `ls`; unsuitable for unattended or production use.
- Effort: low.

Selection required before final NFRs and implementation are frozen.
