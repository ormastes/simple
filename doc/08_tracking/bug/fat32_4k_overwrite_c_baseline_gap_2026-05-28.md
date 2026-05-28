# FAT32 4K Overwrite C Baseline Gap — 2026-05-28

## Status

Open. This blocks claiming Simple FAT 4K random read/write parity or superiority
against the focused C FAT32 baseline.

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
- VFAT baseline still skipped because `scripts/perf/prepare-fat32-4k-vfat.shs`
  is missing.

The gate still fails with:

```text
FAIL: simple_fat32 is not faster than direct C FAT32 for both 4K random read/write p50
```

## Likely Cause

The clean overwrite fast path avoids dirty-cache bookkeeping for full-cluster
overwrites, but the shared FAT path still writes through the block-device sector
interface. The C baseline uses a direct 4096-byte `pwrite` style path, so the
remaining write gap is likely in per-sector dispatch/copy overhead or the lack
of a block-device multi-sector/direct 4K write primitive.

## Required Fix

- Add or route through a production-appropriate multi-sector/direct 4K block
  write path for full-cluster FAT overwrites, or justify why the benchmark
  should compare against the production direct-I/O path instead of the current
  synthetic C baseline.
- Add the missing VFAT preparation path so the stronger C/VFAT claim has real
  same-device evidence.
- Re-run `scripts/perf/run-fat32-4k-cfat-baseline.shs` and record p50/p99 read
  and write results.
