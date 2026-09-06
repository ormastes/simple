# UP2 board image is not byte-reproducible

Status: FIXED
Date: 2026-08-22

## Observation

Two builds with identical kernel SHA-256
`0a8afd63b50bc57792d43cf6e06a643fc2d22d62e7de608b8629137c92293c08`
and resident-loader PE SHA-256
`2b116981f5723371bb3520036fc1deb1ab0a2b6fb01dbecdeb17df61606a936e`
produced different 256 MiB image hashes (`652d5d53…cdf08d` and
`6d947ef3…c2e6b5`). The build script currently labels the image reproducible.

## Likely variable fields

- GPT disk and partition GUID generation by `sgdisk`.
- FAT volume ID and directory/file timestamps from `mkfs.vfat`/mtools.
- Any timestamp retained inside the GRUB standalone image despite identical
  observed loader/kernel inputs.

## Required fix and acceptance

Pin a documented `SOURCE_DATE_EPOCH`, GPT GUIDs, FAT volume ID, and copied-file
timestamps. Build twice into fresh output directories and require identical
full-image SHA-256 while retaining the structural, GRUB-fallback, and resident
DCI-admission gates. Until then, receipts must bind the exact image hash and
also record the independently stable kernel and resident-loader hashes; do not
infer runtime equivalence from image size alone.

## Resolution

The builder now defaults `SOURCE_DATE_EPOCH` to `1704067200`, exports UTC,
sets deterministic disk/partition GUIDs, invokes `mkfs.vfat --invariant` with
fixed ID `53494D50`, and lets SOURCE_DATE_EPOCH govern mtools directory/file
timestamps. The structural checker requires those exact identifiers.

`scripts/check/check-simpleos-up-squared-apollo-lake.shs
--image-reproducibility` built twice into independent fresh directories and
compared the full image plus ESP, resident PE, GRUB fallback, startup script,
and ELF32 shim byte-for-byte. It also rejects a stale system-policy fixture when
its kernel hash or byte length differs from the admitted kernel. PASS image SHA-256:
`abffdd3f668f075385756b1e528605950d782ee95f821bca241c13f259de93fe`.
The deterministic canonical image then passed structural admission (10 checks),
GRUB-fallback OVMF boot/VFS `ls /`, and resident GDB-authored RAM boot.
