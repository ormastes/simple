# Duplicate Checker Baseline Benchmark

**Date:** 2026-03-14
**Binary:** `bin/release/simple` (22MB, compiled 2026-03-14 01:33)
**Script:** `src/compiler/90.tools/duplicate_check/run_check.spl` (token-based, 544 lines)
**Method:** `time timeout <T> bin/simple run_check.spl <dir> 5`

## Results

| Dir | Run | Files | Windows | Dup Groups | Dup Lines | Wall Clock |
|-----|-----|-------|---------|------------|-----------|------------|
| `00.common/` (small) | 1 | 37 | 6,032 | 77 | 385 | **17.07s** |
| `00.common/` (small) | 2 | 37 | 6,032 | 77 | 385 | **16.91s** |
| `15.blocks/` (medium) | 1 | 26 | 4,367 | 379 | 1,895 | **9.90s** |
| `15.blocks/` (medium) | 2 | 26 | 4,367 | 379 | 1,895 | **9.95s** |
| `40.mono/` (larger) | 1 | 22 | 6,351 | 323 | 1,615 | **17.96s** |
| `40.mono/` (larger) | 2 | — | — | — | — | **CRASH** |
| `10.frontend/` (101 files) | 1 | — | — | — | — | **CRASH** |

## Averages (successful runs)

| Dir | Avg Time | Files | Windows | Dup Groups | Dup Lines |
|-----|----------|-------|---------|------------|-----------|
| `00.common/` | **16.99s** | 37 | 6,032 | 77 | 385 |
| `15.blocks/` | **9.93s** | 26 | 4,367 | 379 | 1,895 |
| `40.mono/` | **17.96s** | 22 | 6,351 | 323 | 1,615 |

## Bug: Non-deterministic crash

After the first successful run, subsequent invocations crash with:
```
error: semantic: array index out of bounds: index is 0 but length is 0
```

**Root cause (likely):** The `tokenize()` function returns 0 tokens for some files
(e.g., empty or comment-only `.spl` files), and line 349 accesses `cur_lines[0]`
without checking that the token array is non-empty:
```
w_starts.push(cur_lines[0])   # crashes when cur_lines is empty
```

This is triggered when the interpreter's compiled cache is stale or when the
binary re-parses the script from source on subsequent runs.

## Observations

1. **Scaling is non-linear:** 00.common (37 files, 6K windows) takes 17s while
   15.blocks (26 files, 4.3K windows) takes only 10s — roughly proportional to
   windows count.
2. **40.mono with 22 files takes 18s** because it has 6,351 windows (large files).
3. **O(n^2) within hash groups** is the bottleneck: the pairwise comparison in
   Phase 3 (lines 401-467) checks all pairs within each hash bucket.
4. **10.frontend (101 files)** could not complete — crashes before windowing.
5. **The crash bug must be fixed** before optimization benchmarking can proceed.
