# UP2 board image is not byte-reproducible

Status: OPEN
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
