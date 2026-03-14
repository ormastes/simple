# Simple Standard Library - jscpd Duplication Report

**Date:** 2026-03-14
**Tool:** jscpd 4.0.5 (token-based matching, Python tokenizer for .spl files)
**Settings:** --min-lines 5 --min-tokens 30 --format python --formats-exts 'python:spl'

---

## Summary Statistics

| Directory | Files | Lines | Clone Pairs | Dup Lines | Dup % |
|-----------|-------|-------|-------------|-----------|-------|
| `common/` | 712 | 145,351 | 1,220 | 25,278 | 17.39% |
| `nogc_sync_mut/` | 635 | 125,284 | 733 | 13,716 | 10.95% |
| `nogc_async_mut/` | 151 | 30,206 | 182 | 2,884 | 9.55% |
| `gc_async_mut/` | 23 | 4,947 | 14 | 326 | 6.59% |
| **TOTAL** | **1,521** | **305,788** | **2,149** | **42,204** | **13.80%** |

---

## Top Duplicates by Size (per directory)

### common/ (Top 15)

| # | Lines | Type | File A [range] | File B [range] |
|---|-------|------|----------------|----------------|
| 1 | 452 | CROSS | parser/parser_expr.spl [8-459] | pure/parser_expr.spl [17-469] |
| 2 | 446 | CROSS | parser/parser.spl [8-453] | pure/parser.spl [9-453] |
| 3 | 164 | CROSS | fault_detection.spl [1-164] | sys/fault_detection.spl [1-164] |
| 4 | 124 | CROSS | csv/transform.spl [277-400] | csv/validate.spl [14-137] |
| 5 | 111 | CROSS | color/blend.spl [155-265] | color/manipulate.spl [90-200] |
| 6 | 97 | CROSS | avro/utilities.spl [14-110] | serialization/serialize.spl [12-111] |
| 7 | 81 | CROSS | parser/ast.spl [1-81] | pure/ast.spl [1-82] |
| 8 | 72 | CROSS | color/convert.spl [146-217] | color/manipulate.spl [107-178] |
| 9 | 58 | CROSS | string_core.spl [192-249] | serialization/serialize.spl [15-74] |
| 10 | 58 | CROSS | string_core.spl [293-350] | regex_engine/char_utils.spl [118-175] |
| 11 | 44 | CROSS | graph/traversal.spl [289-332] | graph/utilities.spl [96-139] |
| 12 | 40 | CROSS | color/convert.spl [271-310] | color/manipulate.spl [139-178] |
| 13 | 40 | INTRA | cert/utilities.spl [223-262] | cert/utilities.spl (other range) |

### nogc_sync_mut/ (Top 10)

| # | Lines | Type | File A [range] | File B [range] |
|---|-------|------|----------------|----------------|
| 1 | 112 | CROSS | test_runner/test_runner_helpers.spl [16-127] | test_runner/test_runner_modes.spl [358-469] |
| 2 | 106 | CROSS | debug/remote/protocol/openocd.spl [122-227] | debug/remote/protocol/t32_gdb_bridge.spl [63-168] |
| 3 | 56 | CROSS | database/test_extended/database.spl [775-830] | database/test_extended/queries.spl [279-334] |
| 4 | 50 | CROSS | database/test_extended/database.spl [380-429] | database/test_extended/tracking.spl [49-96] |
| 5 | 42 | CROSS | database/test_extended/database.spl [219-260] | database/test_extended/runs.spl [11-52] |
| 6 | 41 | CROSS | database/test_extended/database.spl [479-519] | database/test_extended/tracking.spl [149-189] |
| 7 | 38 | CROSS | kafka/protocol.spl [19-56] | kafka/types.spl [390-427] |
| 8 | 37 | CROSS | hooks/detectors/feature.spl [90-126] | hooks/detectors/task.spl [81-117] |
| 9 | 37 | CROSS | database/test_extended/database.spl [344-380] | database/test_extended/tracking.spl [12-48] |

### nogc_async_mut/ (Top 10)

| # | Lines | Type | File A [range] | File B [range] |
|---|-------|------|----------------|----------------|
| 1 | 36 | INTRA | mcp/helpers_compat.spl [675-710] | mcp/helpers_compat.spl [434-674] |
| 2 | 28 | INTRA | mcp/helpers_compat.spl [639-666] | mcp/helpers_compat.spl [434-229] |
| 3 | 23 | CROSS | io/tcp.spl [50-72] | io/udp.spl [36-58] |
| 4 | 22 | INTRA | torch/optim.spl [250-271] | torch/optim.spl [115-135] |
| 5 | 22 | INTRA | mcp/helpers_compat.spl [436-457] | mcp/helpers_compat.spl [203-224] |
| 6 | 19 | INTRA | torch/torch_training.spl [323-341] | torch/torch_training.spl [247-151] |
| 7 | 19 | CROSS | mcp/main.spl [497-515] | mcp/main_lazy_protocol.spl [599-617] |
| 8 | 17 | CROSS | mcp/main.spl [256-272] | mcp/main_lazy_protocol.spl [519-535] |
| 9 | 16 | INTRA | mcp/fileio_main.spl [145-160] | mcp/fileio_main.spl [90-105] |
| 10 | 16 | CROSS | mcp/fileio_main.spl [167-182] | mcp/main_lazy_protocol.spl [12-27] |

### gc_async_mut/ (Top 10)

| # | Lines | Type | File A [range] | File B [range] |
|---|-------|------|----------------|----------------|
| 1 | 27 | CROSS | gpu.spl [55-81] | cuda/mod.spl [33-59] |
| 2 | 22 | INTRA | torch/optim.spl [252-273] | torch/optim.spl [113-133] |
| 3 | 19 | INTRA | torch/torch_training.spl [330-348] | torch/torch_training.spl [254-158] |
| 4 | 16 | CROSS | gpu.spl [20-35] | cuda/ffi.spl [11-29] |
| 5 | 14 | INTRA | torch/torch_training.spl [258-271] | torch/torch_training.spl [145-158] |
| 6 | 14 | INTRA | torch/optim.spl [175-188] | torch/optim.spl [154-167] |
| 7 | 11 | INTRA | gpu.spl [634-644] | gpu.spl [623-413] |

---

## Cross-File vs Intra-File Breakdown

| Directory | Cross-File | Intra-File | Total |
|-----------|-----------|------------|-------|
| `common/` | 436 | 784 | 1,220 |
| `nogc_sync_mut/` | 388 | 345 | 733 |
| `nogc_async_mut/` | ~70 | ~112 | 182 |
| `gc_async_mut/` | 3 | 11 | 14 |

---

## Hotspot Files (Most Cross-File Clone Involvement)

### common/
| Clones | File |
|--------|------|
| 18 | trie/utilities.spl |
| 16 | xml/utilities.spl |
| 15 | crypto/sha256.spl |
| 14 | parser/lexer.spl |
| 14 | pure/lexer.spl |
| 14 | linear_algebra/utilities.spl |
| 13 | crypto/sha512.spl |
| 12 | parser/parser_expr.spl |
| 12 | linear_algebra/matrix_ops.spl |
| 11 | xml/xpath.spl |

### nogc_sync_mut/
| Clones | File |
|--------|------|
| 66 | dap/adapter/trace32.spl |
| 40 | database/test_extended/database.spl |
| 37 | dap/adapter/t32_gdb.spl |
| 28 | dap/adapter/openocd.spl |
| 24 | database/test_extended/queries.spl |
| 22 | dap/adapter/gdb_mi.spl |
| 20 | debug/remote/feature/register_trace32.spl |
| 18 | examples/benchmarks/set_operations.spl |
| 16 | debug/remote/backend.spl |
| 15 | examples/testing/integration_example.spl |

### nogc_async_mut/
| Clones | File |
|--------|------|
| 8 | mcp/main_lazy_protocol.spl |
| 8 | llm/provider.spl |
| 6 | mcp/main.spl |
| 6 | llm/mod.spl |
| 4 | mcp/main_lazy.spl |
| 4 | llm/openai_api.spl |
| 3 | mcp/helpers.spl |
| 3 | mcp/helpers_compat.spl |
| 3 | llm/claude_api.spl |
| 3 | io/tcp.spl |

### gc_async_mut/
| Clones | File |
|--------|------|
| 2 | gpu.spl |
| 1 | cuda/ffi.spl |
| 1 | cuda/mod.spl |

---

## Highest Internal Duplication % (per directory, min 10 dup lines)

### common/
| Dup % | Dup/Total Lines | Clones | File |
|-------|-----------------|--------|------|
| 152.7% | 84/55 | 9 | pure/tensor_factory.spl |
| 140.4% | 226/161 | 11 | csv/validate.spl |
| 138.7% | 276/199 | 8 | color/manipulate.spl |
| 127.4% | 795/624 | 39 | pure/parser_expr.spl |
| 122.9% | 236/192 | 34 | pure/evaluator_broadcast.spl |
| 116.6% | 527/452 | 14 | pure/parser.spl |
| 100.0% | 163/163 | 1 | sys/fault_detection.spl (exact copy) |
| 100.0% | 613/613 | 14 | parser/parser_expr.spl |
| 100.0% | 163/163 | 1 | fault_detection.spl (exact copy) |

### nogc_sync_mut/
| Dup % | Dup/Total Lines | Clones | File |
|-------|-----------------|--------|------|
| 162.9% | 404/248 | 68 | dap/adapter/trace32.spl |
| 113.3% | 34/30 | 4 | path_platform/windows_msvc.spl |
| 104.3% | 265/254 | 39 | dap/adapter/t32_gdb.spl |
| 99.2% | 131/132 | 5 | database/test_extended/runs.spl |
| 96.2% | 126/131 | 8 | hooks/detectors/task.spl |
| 92.8% | 193/208 | 6 | database/test_extended/tracking.spl |
| 92.2% | 380/412 | 34 | database/test_extended/queries.spl |
| 88.5% | 100/113 | 5 | database/test_extended/core_helpers.spl |
| 86.8% | 779/897 | 46 | database/test_extended/database.spl |

### nogc_async_mut/
| Dup % | Dup/Total Lines | Clones | File |
|-------|-----------------|--------|------|
| 48.9% | 156/319 | 18 | llm/provider.spl |
| 47.3% | 157/332 | 23 | mcp/debug_log_tools.spl |
| 46.4% | 337/727 | 29 | mcp/helpers_compat.spl |
| 36.3% | 73/201 | 7 | mcp/fileio_main.spl |
| 35.7% | 65/182 | 8 | llm/openai_api.spl |
| 30.3% | 84/277 | 6 | torch/optim.spl |
| 28.4% | 56/197 | 8 | llm/json_helpers.spl |
| 27.7% | 180/649 | 28 | mcp/main_lazy_debug_tools.spl |
| 26.9% | 104/387 | 16 | mcp/debug_eval.spl |

### gc_async_mut/
| Dup % | Dup/Total Lines | Clones | File |
|-------|-----------------|--------|------|
| 46.9% | 15/32 | 1 | cuda/ffi.spl |
| 33.8% | 26/77 | 1 | cuda/mod.spl |
| 30.1% | 84/279 | 6 | torch/optim.spl |
| 19.0% | 88/463 | 8 | torch/torch_training.spl |
| 13.8% | 113/819 | 12 | gpu.spl |

---

## Key Patterns and Recommendations

### 1. parser/ vs pure/ near-complete duplication (common/)
- `parser_expr.spl` and `parser.spl` are 95-100% duplicated between `parser/` and `pure/`
- **~980 duplicated lines** in just these two file pairs
- Recommendation: Extract shared parser module, differentiate only the pure/impure interfaces

### 2. fault_detection.spl exact copy (common/)
- `fault_detection.spl` and `sys/fault_detection.spl` are 100% identical (164 lines)
- Recommendation: Delete one, re-export from the other

### 3. DAP adapter massive duplication (nogc_sync_mut/)
- `trace32.spl` (66 clones), `t32_gdb.spl` (37), `openocd.spl` (28), `gdb_mi.spl` (22)
- These adapters share protocol handling, register access, breakpoint management
- Recommendation: Extract `DapAdapterBase` trait with shared protocol logic

### 4. database/test_extended God object (nogc_sync_mut/)
- `database.spl` (897 lines, 86.8% duplicated) contains code that was later split into `queries.spl`, `tracking.spl`, `runs.spl`, `core_helpers.spl` but the original was never cleaned
- Recommendation: Remove duplicated methods from `database.spl`, keep only the split modules

### 5. MCP handler duplication (nogc_async_mut/)
- `helpers_compat.spl`, `main.spl`, `main_lazy_protocol.spl`, `fileio_main.spl` share protocol handling
- Recommendation: Consolidate MCP protocol helpers

### 6. LLM provider duplication (nogc_async_mut/)
- `provider.spl`, `openai_api.spl`, `claude_api.spl` share API call patterns
- Recommendation: Extract shared HTTP/JSON request builder

### 7. torch/optim.spl and torch_training.spl (both nogc_async_mut/ and gc_async_mut/)
- Identical optimizer update patterns duplicated across GC and non-GC variants
- Recommendation: Share via common module or trait

---

## JSON Reports

Raw jscpd JSON reports saved at:
- `/tmp/jscpd-cosine-lib-common/jscpd-report.json`
- `/tmp/jscpd-cosine-lib-nogc-sync-mut/jscpd-report.json`
- `/tmp/jscpd-cosine-lib-nogc-async-mut/jscpd-report.json`
- `/tmp/jscpd-cosine-lib-gc-async-mut/jscpd-report.json`
