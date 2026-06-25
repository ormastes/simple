# FAT32 vs C FAT Benchmark Results

**Date:** 2026-05-27
**Mode:** interpreter (`bin/simple run`)
**Simple FAT32:** in-memory Fat32Core, 4096 sectors x 512 B
**POSIX baseline:** host kernel filesystem (ext4/btrfs) via std.io_runtime
**VFAT baseline:** 64 MiB loopback FAT32 image via Linux VFAT mount

## Per-Workload Comparison

| Workload | Simple p50 | Simple p99 | POSIX p50 | POSIX p99 | S/P Ratio | VFAT p50 | VFAT p99 | S/V Ratio |
|----------|-----------|-----------|----------|----------|----------|---------|---------|----------|
| create | 208252 | 275709 | 1510 | 1750 | 13791% | 734 | 939 | 28372% |
| lookup | 70 | 132569 | 7 | 19 | 1000% | 7 | 27 | 1000% |
| sequential_read | 11 | 18 | 17 | 48 | 64% | 10 | 34 | 110% |
| append | 97798 | 108885 | 1862 | 2878 | 5252% | 839 | 1041 | 11656% |
| delete | 52084 | 82023 | 56 | 101 | 93007% | 11 | 28 | 473490% |
| stat | 96 | 189747 | 2631 | 3197 | 3% | 1938 | 2996 | 4% |
| directory_scan | 15 | 266413 | 2805 | 4231 | 0% | 2406 | 2843 | 0% |
| random_4k_read | 20 | 31 | 10 | 30 | 200% | 11 | 31 | 181% |
| random_4k_overwrite | 768 | 995 | 3505 | 4869 | 21% | 899 | 1605 | 85% |

## Interpretation

- **S/P Ratio** = (Simple p50 / POSIX p50) x 100. Values > 100% mean Simple is slower.
- **S/V Ratio** = (Simple p50 / VFAT p50) x 100. True FAT32-vs-FAT32 comparison.
- Simple FAT32 runs entirely in-process with in-memory block device.
- POSIX baseline uses host kernel file operations (ext4/btrfs, not VFAT).
- VFAT baseline uses Linux kernel VFAT driver on loopback FAT32 image.
- Both measurements include Simple interpreter dispatch overhead.

## Known Limitations

- Interpreter overhead dominates Simple FAT32 timings (~120ms for path resolve).
- Sequential read is faster on Simple due to in-memory block device (no syscalls).
- Compiled-mode benchmarks show ~121 us for metadata open (see vfat comparison doc).
- Root directory limited to 64 entries (4 sectors/cluster x 512B / 32B per entry).

