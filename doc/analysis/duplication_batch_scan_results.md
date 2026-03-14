# Duplication Batch Scan Results

Date: 2026-03-14

Tool: `bin/simple build duplication` (via `cli_entry_full.spl`)
Method: Edited `src/compiler/80.driver/build/duplication.spl` line 68 to scan each region individually.
Note: All completed regions report "1 duplicate group" — the `error: semantic: variable 'code' not found` prevents the summary/SDN report from being written, so detailed group info (file names, line ranges) is unavailable.

## Results Summary

| Region | Files Scanned | Potential Blocks | Duplicate Groups | Status |
|--------|--------------|-----------------|-----------------|--------|
| `00.common/` | 37 | 18,281 | 1 | Completed |
| `10.frontend/parser/` | 4 | 2,885 | 1 | Completed |
| `10.frontend/treesitter/` | 7 | 9,415 | 1 | Completed |
| `10.frontend/core/hir/` | 0 | 0 | 0 | Completed (no .spl) |
| `10.frontend/core/mir/` | 0 | 0 | 0 | Completed (no .spl) |
| `10.frontend/core/wffi/` | 2 | 562 | 1 | Completed |
| `10.frontend/desugar/` | 10 | 11,336 | 1 | Completed |
| `10.frontend/core/interpreter/` | 19 | — | — | **TIMEOUT (>300s)** |
| `15.blocks/` | 25 | 8,876 | 1 | Completed |
| `20.hir/` | 19 | 16,774 | 1 | Completed |
| `25.traits/` | 9 | 6,496 | 1 | Completed |
| `30.types/type_check/` | 2 | 228 | 1 | Completed |
| `30.types/type_infer/` | 10 | — | — | **TIMEOUT (>300s)** |
| `30.types/type_system/` | 11 | — | — | **TIMEOUT (>300s)** |
| `35.semantics/lint/` | 15 | 12,372 | 1 | Completed |
| `35.semantics/macro_check/` | 4 | 2,860 | 1 | Completed |
| `35.semantics/semantics/` | 5 | 1,341 | 1 | Completed |
| `40.mono/` | 22 | 17,609 | 1 | Completed |

## Timed-Out Regions

Three sub-regions consistently exceed 300 seconds:

1. **`10.frontend/core/interpreter/`** — 19 files, 7,987 lines
2. **`30.types/type_infer/`** — 10 files, 2,567 lines
3. **`30.types/type_system/`** — 11 files, 4,196 lines

The timeout is caused by the `find_duplicates()` grouping algorithm, not file I/O.
Even `10.frontend/` as a whole (94 files) times out due to 124,713 potential duplicate blocks.

## Known Issues

- `error: semantic: variable 'code' not found` — interpreter bug prevents `print_duplication_summary()` from executing. The scan itself completes, but the SDN report is not written and detailed duplicate group info (file paths, line ranges) is not available.
- The `.smf` pre-compiled cache at `src/app/build/duplication.smf` must be removed for source edits to take effect.
- Every completed region reports exactly 1 duplicate group, suggesting the grouping threshold (`min_tokens=30`, `min_lines=5`, `min_impact=100`) filters aggressively.
