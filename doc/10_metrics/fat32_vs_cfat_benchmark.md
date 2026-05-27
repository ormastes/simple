# FAT32 vs C FAT Benchmark Results

**Date:** 2026-05-27
**Mode:** interpreter (`bin/simple run`)
**Simple FAT32:** in-memory Fat32Core, 4096 sectors x 512 B
**POSIX baseline:** host kernel filesystem (ext4/btrfs) via std.io_runtime

## Per-Workload Comparison

| Workload | Simple p50 | Simple p99 | POSIX p50 | POSIX p99 | S/P Ratio |
|----------|-----------|-----------|----------|----------|----------|
| create | 278565 | 544101 | 1616 | 2198 | 17237% |
| lookup | 130024 | 191189 | 13 | 34 | 1000184% |
| sequential_read | 36 | 46 | 44 | 86 | 81% |
| append | 145154 | 159338 | 2797 | 4894 | 5189% |
| delete | 160646 | 190240 | 66 | 130 | 243403% |
| stat | 123831 | 162427 | 2321 | 3527 | 5335% |
| directory_scan | 353600 | 505998 | 2614 | 3211 | 13527% |

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

