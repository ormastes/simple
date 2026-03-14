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

## Layers 50-99 Results (Agent 2)

Scanned by second agent using `bin/simple src/compiler/80.driver/build/cli_entry_full.spl duplication` (direct interpreted execution, bypasses dispatch layer).

| Region | Files Scanned | Potential Blocks | Duplicate Groups | Status |
|--------|--------------|-----------------|-----------------|--------|
| `50.mir/` | 17 | 16,937 | 1 | Completed |
| `55.borrow/` | 10 | 9,611 | 1 | Completed |
| `60.mir_opt/` | 23 | 22,561 | 1 | Completed |
| `70.backend/linker/` | 28 | 28,526 | 1 | Completed |
| `70.backend/backend/native/` | 26 | 36,910 | 1 | Completed |
| `70.backend/backend/common/` | 16 | 4,306 | 1 | Completed |
| `70.backend/backend/wasm/` | 5 | 3,597 | 1 | Completed |
| `70.backend/backend/cuda/` | 5 | 3,760 | 1 | Completed |
| `70.backend/backend/vulkan/` | 3 | 2,557 | 1 | Completed |
| `70.backend/backend/vhdl/` | 3 | 1,520 | 1 | Completed |
| `70.backend/backend/` (full) | 131 | — | — | **TIMEOUT (>300s)** |
| `70.backend/baremetal/` | 5 | 4,576 | 1 | Completed |
| `70.backend/irdsl/` | 4 | 1,251 | 1 | Completed |
| `70.backend/target/` | 2 | 1,196 | 1 | Completed |
| `80.driver/build/` | 38 | — | — | **TIMEOUT (>300s)** |
| `80.driver/watcher/` | 7 | 2,322 | 1 | Completed |
| `80.driver/shb/` | 7 | — | — | **TIMEOUT (>300s)** |
| `80.driver/cache/` | 6 | 2,486 | 1 | Completed |
| `80.driver/driver/` | 3 | 2,332 | 1 | Completed |
| `80.driver/pipeline/` | 2 | 202 | 1 | Completed |
| `85.mdsoc/checker_types/` | 4 | 248 | 1 | Completed |
| `85.mdsoc/construct_types/` | 7 | 763 | 1 | Completed |
| `85.mdsoc/weaving/` | 9 | 398 | 1 | Completed |
| `85.mdsoc/adapters/` | 11 | 1,492 | 1 | Completed |
| `85.mdsoc/types/` | 15 | 1,515 | 1 | Completed |
| `85.mdsoc/transform/` | 30 | 728 | 1 | Completed |
| `85.mdsoc/feature/` | 65 | 556 | 1 | Completed |
| `90.tools/stats/` | 11 | 6,327 | 1 | Completed |
| `90.tools/verify/` | 11 | — | — | **TIMEOUT (>300s)** |
| `95.interp/` | 14 | — | — | **TIMEOUT (>300s)** |
| `99.loader/` | 23 | — | — | **TIMEOUT (>300s)** |

### Not scanned (90.tools remaining subdirs)

| Region | Files | Status |
|--------|-------|--------|
| `90.tools/ffi_gen/` | 71 | Not scanned (too large) |
| `90.tools/fix/` | 19 | Not scanned |
| `90.tools/duplicate_check/` | 18 | Not scanned |
| `90.tools/leak_check/` | 9 | Not scanned |
| `90.tools/leak_finder/` | 8 | Not scanned |
| `90.tools/depgraph/` | 6 | Not scanned |
| `90.tools/perf/` | 5 | Not scanned |
| `90.tools/migrate/` | 2 | Not scanned |
| `90.tools/lint/` | 1 | Not scanned |
| `90.tools/formatter/` | 1 | Not scanned |

### Layers 50-99 Timed-Out Regions

Six sub-regions timed out (process killed during `find_duplicates()` grouping):

1. **`70.backend/backend/`** (full) — 131 files (scanned in sub-batches instead)
2. **`80.driver/build/`** — 38 files
3. **`80.driver/shb/`** — 7 files
4. **`90.tools/verify/`** — 11 files
5. **`95.interp/`** — 14 files
6. **`99.loader/`** — 23 files

### Layers 50-99 Summary

- **Completed scans:** 25 regions
- **Timed out:** 6 regions
- **Not scanned:** 10 regions (90.tools remaining subdirs)
- **Total files scanned:** ~367 files across completed regions
- **Total potential blocks:** ~156,368 across completed regions
- **Every completed region reports exactly 1 duplicate group** (same pattern as layers 00-40)

## Known Issues

- `error: semantic: variable 'code' not found` — interpreter bug prevents `print_duplication_summary()` from executing. The scan itself completes, but the SDN report is not written and detailed duplicate group info (file paths, line ranges) is not available.
- The `.smf` pre-compiled cache at `src/app/build/duplication.smf` must be removed for source edits to take effect.
- Every completed region reports exactly 1 duplicate group, suggesting the grouping threshold (`min_tokens=30`, `min_lines=5`, `min_impact=100`) filters aggressively.
- Running two `bin/simple` interpreter instances concurrently causes severe slowdowns (module loading takes 10x longer due to resource contention).
- The `find_duplicates()` grouping algorithm has worst-case behavior on certain file sets, causing timeouts even on small directories (7 files in `80.driver/shb/`).
