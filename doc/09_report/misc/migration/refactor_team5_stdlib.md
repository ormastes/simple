# Team 5: stdlib Refactoring Analysis Report
## Region: `src/lib/` (~1546 files, ~355K lines)

---

## 1. FILE_SIZE_VIOLATIONS (>800 lines)

| File | Lines | Proposed Split |
|------|-------|----------------|
| `nogc_sync_mut/database/test_extended/database.spl` | 899 | Split into `database_queries.spl` (list_runs, all_test_info, get_timing_summary ~L700-899) and `database_recording.spl` (record_result, update_timing, update_counters ~L350-700). Note: file comment says "All methods consolidated for bootstrap runtime compatibility" -- verify bootstrap can handle `impl` blocks from separate modules before splitting. |
| `nogc_sync_mut/ffi/llvm.spl` | 878 | Split by LLVM subsystem: `llvm_types.spl` (type constructors, ~L200-350), `llvm_instructions.spl` (arithmetic/memory/control ~L400-600), `llvm_target.spl` (target machine, emit, ~L700-878). 142 public functions -- clear section markers already exist. |
| `nogc_sync_mut/src/tooling/easy_fix/rules.spl` | 849 | **Already split in `common/tooling/easy_fix/`** into rules_lint (423), rules_structural (202), rules_compiler (120), rules_helpers (117), rules.spl orchestrator (94). The nogc_sync_mut version is the OLD monolith -- migrate to use the common split version. |
| `gc_async_mut/gpu.spl` | 820 | Split into `gpu_device.spl` (init, device queries, context ~L1-200), `gpu_memory.spl` (alloc, free, upload, download ~L200-410), `gpu_intrinsics.spl` (block/thread ID stubs ~L411-600), `gpu_kernel.spl` (launch, module load ~L600-820). 101 public functions. |

## 2. WATCH_LIST (600-800 lines)

| File | Lines | Risk |
|------|-------|------|
| `common/pure/evaluator.spl` | 780 | 20 public fns, approaching limit |
| `nogc_sync_mut/amqp_utils.spl` | 740 | 95 public fns -- very high API surface |
| `common/search_utils.spl` | 740 | 31 public fns |
| `nogc_sync_mut/src/di.spl` | 738 | Dependency injection -- class-heavy, 0 top-level fns |
| `nogc_async_mut/mcp/helpers_compat.spl` | 728 | Compatibility layer |
| `nogc_async_mut/mcp/resources.spl` | 727 | MCP resources |
| `common/math_repr.spl` | 725 | 37 public fns |
| `common/matrix_utils.spl` | 721 | 34 public fns |
| `nogc_sync_mut/lsp/lsp_handlers.spl` | 719 | 35 public fns -- natural split by LSP method type |
| `nogc_sync_mut/udp_utils.spl` | 716 | 72 public fns |
| `common/sdn/parser.spl` | 708 | SDN parser core |
| `nogc_sync_mut/src/infra.spl` | 703 | Infrastructure |
| `nogc_sync_mut/src/tensor.spl` | 695 | 94 public fns |
| `common/comparator_utils.spl` | 693 | |
| `common/fenwick_tree/utilities.spl` | 690 | |
| `common/stats_utils.spl` | 688 | |
| `nogc_sync_mut/binary_io.spl` | 684 | |
| `common/pure/nn/functional.spl` | 684 | |

## 3. DUPLICATION

### 3a. easy_fix/rules.spl Duplication (HIGH PRIORITY)
- **`nogc_sync_mut/src/tooling/easy_fix/rules.spl`** (849 lines, monolith) contains 12 `check_*` functions
- **`common/tooling/easy_fix/`** has the properly split version (956 total lines across 5 files) with 9 `check_*` functions
- The common version is the refactored target. The nogc_sync_mut monolith should be replaced with a thin re-export that delegates to `common/tooling/easy_fix/rules.spl`.

### 3b. torch/backend.spl Triplication (MEDIUM PRIORITY)
Three near-identical files (~287 lines each, ~866 lines total):
- `nogc_sync_mut/torch/backend.spl` (287 lines)
- `nogc_async_mut/torch/backend.spl` (287 lines)
- `gc_async_mut/torch/backend.spl` (292 lines)

Diff shows only comment headers and import paths differ. The actual TorchBackend operations are identical handle-level FFI calls. **Resolution:** Extract shared logic into `common/torch/backend_ops.spl`, have each variant import and adapt.

### 3c. `kafka/types.spl` Oversized API
- `nogc_sync_mut/kafka/types.spl` has **151 function/method definitions** -- highest in all of `src/lib/`. Likely contains message builder, serialization, and protocol types that should be in separate files.

## 4. CROSS_MODULE_COUPLING

### Violations Found
**`nogc_sync_mut` -> `nogc_async_mut`:** 10+ files in `nogc_sync_mut/mcp/handlers/` import heavily from `nogc_async_mut/mcp/`:
- `debug_handler.spl` imports `SessionManager` + 18 debug handlers from `nogc_async_mut`
- `diag_handler.spl` imports read/edit/vcs tools from `nogc_async_mut`
- `debug_log_handler.spl` imports debug log tools from `nogc_async_mut`
- `api_handler.spl` imports `handle_simple_api` from `nogc_async_mut`
- `jj/helpers.spl` imports ~40 helper functions from `nogc_async_mut`

**Assessment:** The `mcp/handlers/` directory in `nogc_sync_mut` acts as a sync facade over async MCP implementations. This is an architectural decision, not a bug -- but the dependency direction is inverted (sync depends on async). Consider moving these handler files to `nogc_async_mut` or creating a dedicated `mcp_handlers` module.

**`gc_async_mut` -> `common`:** `gc_async_mut/torch/` imports from `common/torch/` -- this is the CORRECT direction (gc can depend on common).

**`nogc_async_mut` -> `nogc_sync_mut`:** No violations found (clean).
**`nogc_sync_mut` -> `gc_async_mut`:** No violations found (clean).
**`common` -> any mutable module:** No violations found (clean).

## 5. COUPLING_HOTSPOTS (highest fan-out)

| Imports | File |
|---------|------|
| 20 | `nogc_sync_mut/test_runner/test_runner_main.spl` |
| 19 | `nogc_sync_mut/test_runner/main.spl` |
| 19 | `nogc_sync_mut/io.spl` |
| 18 | `nogc_sync_mut/net/__init__.spl` |
| 17 | `nogc_async_mut/async_host/__init__.spl` |
| 15 | `nogc_sync_mut/test_runner/test_executor_composite_jit_generic.spl` |
| 15 | `nogc_sync_mut/engine/core/engine.spl` |
| 15 | `nogc_sync_mut/debug/remote/backend_arm.spl` |

### Public API Surface Hotspots (>15 fn/method defs)

| Defs | File |
|------|------|
| 151 | `nogc_sync_mut/kafka/types.spl` |
| 142 | `nogc_sync_mut/ffi/llvm.spl` |
| 120 | `gc_async_mut/gpu.spl` |
| 105 | `nogc_sync_mut/ftp_utils.spl` |
| 95 | `nogc_sync_mut/amqp_utils.spl` |
| 94 | `nogc_sync_mut/src/tensor.spl` |
| 93 | `common/statistics/mod.spl` |
| 85 | `common/torch/dyn_ffi_ops.spl` |

## 6. BIGO_FLAGS

### O(n^2) List Building via Concatenation
**Pattern:** `list = list + [item]` inside a loop creates a new list each iteration = O(n^2).

| File:Line | Pattern | Severity |
|-----------|---------|----------|
| `compression/gzip/inflate.spl:48` | `block_data = block_data + [data[...]]` in loop | HIGH -- decompression hot path |
| `compression/types.spl:58,93,125,134` | `nodes = nodes + [leaf]` in Huffman tree build | HIGH -- O(n^2) tree construction |
| `compression/types.spl:162` | `new_codes = codes + [[ch, code]]` | MEDIUM |
| `compression/gzip/huffman.spl:201` | `result = codes + [[symbol, code_bits, code_len]]` | MEDIUM |
| `database/sql/statement.spl:136,146,149` | Column/row building via concatenation | MEDIUM |
| `database/sql/stmt_cache.spl:57,95,102,119` | Cache order list rebuilds | LOW |
| `io/debug_state.spl:68,86,103,234` | Breakpoint/watch list building | LOW (small lists) |
| `io/sqlite_ffi.spl:204,212,215` | Query result building | MEDIUM |
| `kafka/serialization.spl:71,212` | Byte buffer building | HIGH -- serialization hot path |
| `io/tcp.spl:56` | `result = result + [data[i]]` | MEDIUM |

**Fix:** All should use `list.push(item)` instead of `list = list + [item]`.

### O(n^2) Huffman Tree Construction
`compression/types.spl` lines 50-134: The Huffman tree builder uses repeated linear scans to find minimums + list rebuilds via concatenation. Each iteration is O(n) for min-find and O(n) for list rebuild, across n iterations = **O(n^3)** overall. Should use a priority queue/min-heap.

### String Concatenation in Loops
| File:Line | Pattern |
|-----------|---------|
| `src/core/decorators.spl:142-158` | `args_str = args_str + ", " + "{arg}"` repeated 4x | LOW (bounded) |
| `compression/types.spl:169-170` | `huffman_traverse` recursive `code + "0"` / `code + "1"` | MEDIUM -- creates O(depth) intermediate strings |

### `.contains()` on Lists in Loops
| File:Line | Pattern |
|-----------|---------|
| `lazy/transform.spl:272` | `if not seen.contains(elem)` -- dedup via linear scan = O(n^2) | MEDIUM |
| `iterator/reduce.spl:390` | `if not groups.contains(key)` -- group-by via linear scan | MEDIUM |
| `lazy/utilities.spl:53,76` | `cache.contains(key)` -- cache lookup is O(n) if cache is a list | MEDIUM |
| `report/compiler/easy_fix.spl:210,287` | `files.contains(...)` | LOW |

## 7. RECOMMENDATIONS (Prioritized)

### P0 -- Critical (performance bugs)
1. **Fix O(n^2) list building in compression/** -- Replace `list = list + [item]` with `list.push(item)` in `inflate.spl`, `types.spl`, `huffman.spl`. These are data-processing hot paths.
2. **Fix O(n^3) Huffman tree build** in `compression/types.spl` -- Use a min-heap or at minimum use `.push()` instead of concatenation for the list rebuilds.
3. **Fix O(n^2) patterns in kafka/serialization.spl** -- Byte buffer building via concatenation.

### P1 -- High (duplication/maintainability)
4. **Retire `nogc_sync_mut/src/tooling/easy_fix/rules.spl` monolith** (849 lines) -- Replace with thin re-export delegating to the already-split `common/tooling/easy_fix/` modules. Saves 849 lines of duplicated logic.
5. **Extract shared torch backend** -- The 3 near-identical `torch/backend.spl` files (866 total lines) should share a common implementation in `common/torch/backend_ops.spl`.
6. **Split `ffi/llvm.spl`** (878 lines, 142 fns) into 3 files by LLVM subsystem. Section markers already exist.
7. **Split `gpu.spl`** (820 lines, 101 fns) into device/memory/intrinsics/kernel modules.

### P2 -- Medium (architectural)
8. **Resolve `nogc_sync_mut` -> `nogc_async_mut` coupling** in `mcp/handlers/` -- Move the 5+ handler files to `nogc_async_mut` where their dependencies live, or create a `mcp_facade` module that explicitly bridges the two.
9. **Split `database/test_extended/database.spl`** (899 lines) -- Verify bootstrap runtime can handle split impl blocks first (file comment warns against this).
10. **Tame `kafka/types.spl`** (151 defs) -- Split by concern: message types, protocol types, config types.

### P3 -- Low (watch items)
11. **Monitor watch-list files** approaching 800 lines (18 files in 600-780 range).
12. **Replace `.contains()` on lists** with set/map lookups in `lazy/transform.spl` and `iterator/reduce.spl` for dedup/group-by operations.
13. **Fix list concatenation** in `database/sql/`, `io/sqlite_ffi.spl`, `io/tcp.spl` -- less critical paths but still O(n^2).
