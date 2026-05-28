# FAT32 4K Overwrite C Baseline Gap — 2026-05-28

## Status

Partially resolved. The latest focused run passes against the direct C FAT32
baseline, but the stronger C/VFAT same-device claim remains blocked until a
writable seeded VFAT mount is available.

## Evidence

`scripts/perf/run-fat32-4k-cfat-baseline.shs` was run before and after adding a
clean full-cluster overwrite path in
`src/lib/nogc_async_mut/fs_driver/fat32_core.spl`.

Before the change:

- Simple FAT32 4K read: p50 13us, p99 14us.
- Simple FAT32 4K write: p50 35us, p99 41us.
- Direct C FAT32 4K read: p50 34us, p99 62us.
- Direct C FAT32 4K write: p50 29us, p99 65us.
- VFAT baseline was skipped because `scripts/perf/prepare-fat32-4k-vfat.shs`
  is missing.

After adding `Fat32Core.write_cluster_clean()` and routing full aligned
`write_4k_overwrite_at()` / `write_4k_overwrite_cluster_at()` calls through it:

- Simple FAT32 4K read: p50 13us, p99 14us.
- Simple FAT32 4K write: p50 34us, p99 37us.
- Direct C FAT32 4K read: p50 27us, p99 64us.
- Direct C FAT32 4K write: p50 26us, p99 53us.
- VFAT baseline still skipped because no seeded writable VFAT mount was
  available to the benchmark in that run.

Latest local run after confirming the benchmark no longer crashes:

- Simple FAT32 4K read: p50 13us, p99 21us.
- Simple FAT32 4K write: p50 39us, p99 42us.
- Direct C FAT32 4K read: p50 32us, p99 76us.
- Direct C FAT32 4K write: p50 26us, p99 46us.
- VFAT baseline skipped because `/tmp/simple_vfat_bench_mnt` is mounted but
  root-owned and unseeded for this user. `scripts/perf/prepare-fat32-4k-vfat.shs`
  failed locally because passwordless sudo is unavailable for remount/reseed.

Latest isolated local rerun:

- Simple FAT32 4K read: p50 12us, p99 19us.
- Simple FAT32 4K write: p50 34us, p99 37us.
- Direct C FAT32 4K read: p50 40us, p99 71us.
- Direct C FAT32 4K write: p50 45us, p99 84us.
- `scripts/perf/run-fat32-4k-cfat-baseline.shs` passed the direct C comparison.
- VFAT baseline still skipped because `/tmp/simple_vfat_bench_mnt` is missing
  seeded writable files for this user.
- The VFAT-required run now fails cleanly with `FAILED: VFAT baseline is
  required but missing or unseeded` instead of treating `SKIPPED` rows as
  integer p50 values.
- `scripts/perf/prepare-fat32-4k-vfat.shs` now has a `udisksctl` fallback when
  the target mount point is free, but the current host is still blocked because
  `/tmp/simple_vfat_bench_mnt` is already mounted root-owned and passwordless
  sudo is unavailable to remount it for this user.

The C gate now passes with:

```text
PASS: simple_fat32 is faster than direct C FAT32 for 4K random read/write p50
```

## Likely Cause

The clean overwrite fast path avoids dirty-cache bookkeeping for full-cluster
overwrites. The remaining release blocker is not the direct C comparison on the
latest run; it is lack of VFAT same-device evidence in this local environment.

## Required Fix

- Run `scripts/perf/prepare-fat32-4k-vfat.shs` on a writable VFAT mount or
  remount the local loop device with `uid=$(id -u),gid=$(id -g)`.
- Re-run `REQUIRE_VFAT_BASELINE=1 scripts/perf/run-fat32-4k-cfat-baseline.shs`
  and record p50/p99 read and write results.
