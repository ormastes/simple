# FAT32 vs C FAT (POSIX) Benchmark Results

**Date:** 2026-05-26
**Mode:** interpreter (`bin/simple run`)
**Simple FAT32:** in-memory Fat32Core, 4096 sectors x 512 B
**C FAT baseline:** host kernel POSIX filesystem via std.io_runtime

## Per-Workload Comparison

| Workload | Simple p50 (us) | Simple p99 (us) | POSIX p50 (us) | POSIX p99 (us) | Ratio p50 |
|----------|----------------|----------------|----------------|----------------|-----------|
| create | 260762 | 386692 | 1974 | 3018 | 13209% |
| lookup | 123514 | 136858 | 12 | 23 | 1029283% |
| sequential_read | 26 | 35 | 26 | 51 | 100% |
| append | 138436 | 139720 | 3017 | 3121 | 4588% |
| delete | 155949 | 168781 | 56 | 93 | 278480% |
| stat | 119988 | 121262 | 2453 | 2879 | 4891% |
| directory_scan | 317243 | 450109 | 2013 | 2906 | 15759% |

## Interpretation

- **Ratio** = (Simple p50 / POSIX p50) x 100. Values > 100% mean Simple is slower.
- **SKIP** = workload could not complete (directory full or other runtime error).
- Simple FAT32 runs entirely in-process with in-memory block device.
- POSIX baseline uses host kernel file operations (ext4/btrfs, not VFAT).
- Both measurements include Simple interpreter dispatch overhead.
- For compiled-mode estimates, see fs_driver_vfat_comparison.md.

## Known Limitations

- Interpreter overhead dominates Simple FAT32 timings (~120ms for path resolve).
- Sequential read is faster on Simple due to in-memory block device (no syscalls).
- Compiled-mode benchmarks show ~121 us for metadata open (see vfat comparison doc).
- Root directory limited to 64 entries (4 sectors/cluster x 512B / 32B per entry).

