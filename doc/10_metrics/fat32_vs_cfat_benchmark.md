# FAT32 vs C FAT Benchmark Results

**Date:** 2026-05-27
**Mode:** interpreter (`bin/simple run`)
**Simple FAT32:** in-memory Fat32Core, 4096 sectors x 512 B
**POSIX baseline:** host kernel filesystem (ext4/btrfs) via std.io_runtime

## Per-Workload Comparison

| Workload | Simple p50 | Simple p99 | POSIX p50 | POSIX p99 | S/P Ratio |
|----------|-----------|-----------|----------|----------|----------|
| create | 268561 | 506766 | 2106 | 2544 | 12752% |
| lookup | 123937 | 195471 | 17 | 31 | 729041% |
| sequential_read | 20 | 29 | 37 | 58 | 54% |
| append | 141603 | 186923 | 2478 | 2971 | 5714% |
| delete | 160094 | 182824 | 68 | 132 | 235432% |
| stat | 196141 | 198159 | 2922 | 4759 | 6712% |
| directory_scan | 500658 | 505772 | 2587 | 3663 | 19352% |

## Interpretation

- **S/P Ratio** = (Simple p50 / POSIX p50) x 100. Values > 100% mean Simple is slower.
- Simple FAT32 runs entirely in-process with in-memory block device.
- POSIX baseline uses host kernel file operations (ext4/btrfs, not VFAT).
- Both measurements include Simple interpreter dispatch overhead.

## Known Limitations

- Interpreter overhead dominates Simple FAT32 timings (~120ms for path resolve).
- Sequential read is faster on Simple due to in-memory block device (no syscalls).
- Compiled-mode benchmarks show ~121 us for metadata open (see vfat comparison doc).
- Root directory limited to 64 entries (4 sectors/cluster x 512B / 32B per entry).

