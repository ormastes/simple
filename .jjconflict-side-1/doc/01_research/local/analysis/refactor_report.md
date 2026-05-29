# Consolidated Refactoring Analysis Report

**Date:** 2026-03-25
**Teams:** 6 (Frontend, Middle, Backend, Driver, Stdlib, App)
**Total Scope:** ~2,042 files, ~670K lines across `src/compiler/`, `src/lib/`, `src/app/`

---

## 1. Executive Summary

| Metric | Count |
|--------|-------|
| Total files scanned | ~2,042 |
| Oversized files (>800 lines) | **12** |
| Watch-list files (600-800 lines) | **63** |
| Layer violations | **20** |
| Duplication clusters | **9** |
| Big-O anti-pattern flags | **48+** |
| Coupling hotspots (>15 imports) | **18** |
| Public API hotspots (>50 fns) | **12** |
| P0 critical items | **10** |
| P1 important items | **14** |
| P2 backlog items | **18** |

**Worst Offenders:**
1. `src/app/cli/query_rich.spl` -- 2,421 lines (3x limit), 61 functions, 19 imports
2. `bootstrap_pipeline.spl` -- 785 lines duplicated byte-for-byte across `src/app/` and `src/compiler/80.driver/`
3. `list = list + [item]` anti-pattern -- **60+ instances** across all 6 regions, causing O(n^2) in hot paths
4. `00.common` layer violations -- foundation layer imports from `10.frontend`, `30.types`, and `70.backend`
5. `30.types` -> `35.semantics` layer violation -- 5 files all import `narrowing.*`

---

## 2. P0 Critical Items (Score 18-27) -- Fix Immediately

| # | Description | Files | Action | Score | Team |
|---|-------------|-------|--------|-------|------|
| P0-1 | `query_rich.spl` is 2,421 lines (3x limit) | `src/app/cli/query_rich.spl` | Split into 6 files: `query_rich_lsp.spl`, `query_rich_tokens.spl`, `query_rich_check.spl`, `query_rich_error_codes.spl`, `query_rich_lint.spl`, `query_rich_util.spl` | 27 (3x3x3) | T6 |
| P0-2 | `00.common` imports from `10.frontend`, `30.types`, `70.backend` -- breaks foundational layering | `00.common/attributes.spl`, `00.common/compiler_services.spl` | Extract `Attribute`, `Expr`, `LayoutAttr`, `BackendPort` types into `00.common/` or accept as generic parameters | 27 (3x3x3) | T1 |
| P0-3 | `list = list + [item]` O(n^2) in compression hot paths | `src/lib/*/compression/inflate.spl`, `types.spl`, `huffman.spl` | Replace with `.push()` -- these are data-processing hot paths | 27 (3x3x3) | T5 |
| P0-4 | O(n^3) Huffman tree construction | `src/lib/*/compression/types.spl:50-134` | Use min-heap or priority queue; replace list concat with `.push()` | 27 (3x3x3) | T5 |
| P0-5 | `bootstrap_pipeline.spl` exact duplicate (785 lines x2) | `src/app/build/bootstrap_pipeline.spl`, `src/compiler/80.driver/build/bootstrap_pipeline.spl` | Delete one copy, replace with re-export from the canonical location | 18 (3x3x2) | T4+T6 |
| P0-6 | `50.mir` imports from `70.backend` (upward 2 layers) | `50.mir/mir_lowering_expr.spl` | Move `gpu_intrinsics.is_gpu_intrinsic()` to `00.common` or `30.types` | 18 (3x3x2) | T3 |
| P0-7 | `70.backend` imports from `95.interp` (4 files) | `wasm_backend.spl`, `llvm_backend_tools.spl`, `wasm_linker.spl`, `jit_interpreter.spl` | Extract tool-finding utilities to `70.backend/tool_discovery.spl` | 18 (3x3x2) | T3 |
| P0-8 | O(n^2) array concat in monomorphization hot path | `40.mono/monomorphize/engine.spl:118,138,145` | Replace `arr = arr + [item]` with `.push()` (3 instances) | 18 (3x3x2) | T2 |
| P0-9 | `30.types` -> `35.semantics.narrowing` layer violation (5 files) | `30.types/type_infer/context.spl`, `inference_expr.spl`, `inference_expr_ops.spl`, `type_infer_types.spl`, `type_infer.spl` | Move `narrowing.spl` types to `30.types/` or extract `narrowing_types.spl` | 18 (3x2x3) | T2 |
| P0-10 | O(n^2) kafka serialization byte buffer building | `src/lib/*/kafka/serialization.spl:71,212` | Replace list concat with `.push()` | 18 (3x3x2) | T5 |

---

## 3. P1 Important Items (Score 9-17) -- Fix Next Sprint

| # | Description | Files | Action | Score | Team |
|---|-------------|-------|--------|-------|------|
| P1-1 | `mir_to_llvm.spl` 941 lines | `70.backend/backend/mir_to_llvm.spl` | Split into `mir_to_llvm_core.spl`, `mir_to_llvm_inst.spl`, `mir_to_llvm_runtime.spl` | 12 (2x3x2) | T3 |
| P1-2 | `lint/main.spl` 974 lines | `90.tools/lint/main.spl` | Split into `lint_config.spl`, `lint_rules.spl`, `lint_checks.spl`, `lint_main.spl` | 12 (2x3x2) | T4 |
| P1-3 | `driver.spl` 895 lines, 27 imports from 11 layers | `80.driver/driver.spl` | Extract phases to `driver_phases.spl`, MIR to `driver_mir.spl`; create `pipeline_facade.spl` | 12 (2x3x2) | T4 |
| P1-4 | `eval_ops.spl` 1035 lines | `10.frontend/core/interpreter/eval_ops.spl` | Split into `eval_ops_calls.spl`, `eval_ops_methods.spl`, `eval_ops_access.spl` | 12 (2x3x2) | T1 |
| P1-5 | `error_formatter.spl` has 70 string concat instances | `35.semantics/error_formatter.spl` | Use `List<text>` accumulator + `.join("")` | 12 (2x3x2) | T2 |
| P1-6 | `easy_fix/rules.spl` monolith (849 lines) duplicates split version | `src/lib/nogc_sync_mut/src/tooling/easy_fix/rules.spl` | Replace with thin re-export delegating to `common/tooling/easy_fix/` | 12 (2x3x2) | T5 |
| P1-7 | `ffi/llvm.spl` 878 lines, 142 public functions | `src/lib/nogc_sync_mut/ffi/llvm.spl` | Split into `llvm_types.spl`, `llvm_instructions.spl`, `llvm_target.spl` | 12 (2x3x2) | T5 |
| P1-8 | `gpu.spl` 820 lines, 101 public functions | `src/lib/gc_async_mut/gpu.spl` | Split into `gpu_device.spl`, `gpu_memory.spl`, `gpu_intrinsics.spl`, `gpu_kernel.spl` | 12 (2x3x2) | T5 |
| P1-9 | `widgets.spl` 1,066 lines | `src/app/ui.render/widgets.spl` | Split into `widgets_tui.spl` (~700) + `widgets_html.spl` (~330) | 12 (2x3x2) | T6 |
| P1-10 | Nested loop O(10^9) worst case in asm parser | `10.frontend/core/parser_primary.spl:140+152` | Reduce inner recovery loop to `0..100`, outer to `0..10000` | 9 (3x1x3) | T1 |
| P1-11 | `lexer_scanners.spl:205` loop bound 1,000,000 | `10.frontend/core/lexer_scanners.spl:205` | Reduce to `0..100000` | 9 (3x1x3) | T1 |
| P1-12 | Bubble sort O(n^2) in duplicate detector | `90.tools/duplicate_check/detector.spl:229-244` | Replace with merge sort or sorted insert | 9 (2x3x1.5) | T4 |
| P1-13 | `list = list + [item]` across `90.tools/` (~20 instances) | `detector.spl`, `fix/imports.spl`, `migrate/tests.spl`, `verify/verify_features.spl`, etc. | Replace all with `.push()` | 9 (2x3x1.5) | T4 |
| P1-14 | `70.backend` imports from `80.driver` (3 imports) | `70.backend/build_native_pipeline.spl` | Move file to `80.driver/` or push shared types to `00.common` | 9 (3x1x3) | T3 |

---

## 4. P2 Backlog Items (Score 1-8) -- Nice to Have

| # | Description | Files | Action | Score | Team |
|---|-------------|-------|--------|-------|------|
| P2-1 | `parser_decls.spl` 930 lines | `10.frontend/core/parser_decls.spl` | Extract `parse_module_body()` and `parse_bitfield_decl()` | 8 (2x2x2) | T1 |
| P2-2 | `parser_primary.spl` 850 lines | `10.frontend/core/parser_primary.spl` | Extract ASM parsing to `parser_asm.spl` | 8 (2x2x2) | T1 |
| P2-3 | Create `parser_prelude.spl` | 5 parser files averaging 48 imports each | Re-export common tokens, AST constructors, utilities | 8 (2x2x2) | T1 |
| P2-4 | `variance_types.spl` at 798 lines (imminent breach) | `30.types/variance_types.spl` | Split into core/inference/checking along Phase 6A/6B/6C | 8 (2x2x2) | T2 |
| P2-5 | `dim_constraints.spl` at 779 lines (imminent breach) | `30.types/dim_constraints.spl` | Split `DimSolver` from runtime check generation | 8 (2x2x2) | T2 |
| P2-6 | Torch backend triplicated (866 total lines) | `nogc_sync_mut/torch/backend.spl`, `nogc_async_mut/torch/backend.spl`, `gc_async_mut/torch/backend.spl` | Extract shared logic into `common/torch/backend_ops.spl` | 8 (2x2x2) | T5 |
| P2-7 | Extract `BackendVisitor` trait for shared MIR walk | `cuda_backend.spl`, `wasm_backend.spl`, `c_backend_translate.spl` | Dedup ~150-200 lines per backend | 6 (2x2x1.5) | T3 |
| P2-8 | `database/test_extended/database.spl` 899 lines | `src/lib/nogc_sync_mut/database/test_extended/database.spl` | Split into queries + recording (verify bootstrap compat first) | 6 (2x2x1.5) | T5 |
| P2-9 | HIR type tag constants duplicated | `10.frontend/core/hir_types.spl`, `20.hir/hir_types.spl` | Extract shared constants to `00.common/hir_type_tags.spl` | 6 (2x2x1.5) | T1 |
| P2-10 | `hir_lowering/items.spl` 811 lines | `20.hir/hir_lowering/items.spl` | Split into core/types/traits by lowered item type | 6 (2x2x1.5) | T1 |
| P2-11 | `nogc_sync_mut` -> `nogc_async_mut` coupling (10+ files) | `src/lib/nogc_sync_mut/mcp/handlers/*.spl` | Move handler files to `nogc_async_mut` or create facade | 6 (2x2x1.5) | T5 |
| P2-12 | `kafka/types.spl` 151 function definitions | `src/lib/nogc_sync_mut/kafka/types.spl` | Split by concern: message, protocol, config types | 4 (1x2x2) | T5 |
| P2-13 | `riscv32_asm.spl` 73 public functions | `70.backend/backend/riscv32_asm.spl` | Split into sub-modules by instruction category | 4 (1x2x2) | T3 |
| P2-14 | Delete dead code `im_rs.spl` (276 lines, 25 pass_todo, zero impl) | `90.tools/ffi_gen/specs/im_rs.spl` | Delete or move to `specs/pending/` | 4 (1x2x2) | T4 |
| P2-15 | `10.frontend/frontend.spl` -> `compiler.tools` violation | `10.frontend/frontend.spl` | Move `desugar_async` into `10.frontend/desugar/` | 4 (2x1x2) | T1 |
| P2-16 | `20.hir/inference/infer.spl` -> `compiler.tools` violation | `20.hir/inference/infer.spl` | Move `SuffixRegistry` to `00.common/` or `20.hir/` | 4 (2x1x2) | T1 |
| P2-17 | Replace `.contains()` with Set lookups in multiple files | `call_graph.spl`, `aop.spl`, `generalization.spl`, `lazy/transform.spl`, `isel_context.spl` | Use Set/Dict for O(1) lookups instead of linear scans | 4 (1x2x2) | All |
| P2-18 | Extract error code table from 96-entry if-chain | `src/app/cli/query_rich.spl:1203-1428` | Convert to data-driven lookup map | 4 (1x2x2) | T6 |

---

## 5. File Size Violations -- Complete Table (All Teams)

All files exceeding the 800-line limit, sorted by size descending:

| # | File | Lines | Team | Proposed Resolution |
|---|------|-------|------|---------------------|
| 1 | `src/app/cli/query_rich.spl` | 2,421 | T6 | Split into 6 domain-focused files |
| 2 | `src/app/ui.render/widgets.spl` | 1,066 | T6 | Split TUI vs HTML renderers |
| 3 | `src/compiler/10.frontend/core/interpreter/eval_ops.spl` | 1,035 | T1 | Split into calls/methods/access |
| 4 | `src/compiler/90.tools/lint/main.spl` | 974 | T4 | Split into config/rules/checks/main |
| 5 | `src/compiler/70.backend/backend/mir_to_llvm.spl` | 941 | T3 | Split into core/instructions/runtime |
| 6 | `src/compiler/10.frontend/core/parser_decls.spl` | 930 | T1 | Extract module_body + bitfield_decl |
| 7 | `src/lib/nogc_sync_mut/database/test_extended/database.spl` | 899 | T5 | Split queries + recording |
| 8 | `src/compiler/80.driver/driver.spl` | 895 | T4 | Extract phases + MIR pipeline |
| 9 | `src/lib/nogc_sync_mut/ffi/llvm.spl` | 878 | T5 | Split by LLVM subsystem (types/instructions/target) |
| 10 | `src/compiler/10.frontend/core/parser_primary.spl` | 850 | T1 | Extract ASM parsing |
| 11 | `src/lib/nogc_sync_mut/src/tooling/easy_fix/rules.spl` | 849 | T5 | Replace monolith with re-export to split version |
| 12 | `src/lib/gc_async_mut/gpu.spl` | 820 | T5 | Split device/memory/intrinsics/kernel |
| 13 | `src/compiler/20.hir/hir_lowering/items.spl` | 811 | T1 | Split by lowered item type |

**Near-breach (790-800):**

| File | Lines | Team |
|------|-------|------|
| `src/compiler/30.types/variance_types.spl` | 798 | T2 |
| `src/app/build/bootstrap_pipeline.spl` | 785 | T6 |
| `src/compiler/80.driver/build/bootstrap_pipeline.spl` | 785 | T4 |
| `src/compiler/30.types/dim_constraints.spl` | 779 | T2 |
| `src/app/spipe_docgen/main.spl` | 769 | T6 |

---

## 6. Duplication Catalog

| # | Cluster | Files | Dup Lines | Resolution | Priority |
|---|---------|-------|-----------|------------|----------|
| D1 | **bootstrap_pipeline.spl exact copy** | `src/app/build/bootstrap_pipeline.spl` (785), `src/compiler/80.driver/build/bootstrap_pipeline.spl` (785) | 785 | Delete one copy, re-export from canonical location | P0 |
| D2 | **easy_fix/rules.spl monolith vs split** | `nogc_sync_mut/src/tooling/easy_fix/rules.spl` (849) vs `common/tooling/easy_fix/` (956 across 5 files) | ~849 | Replace monolith with thin re-export to common split | P1 |
| D3 | **torch/backend.spl triplication** | `nogc_sync_mut/torch/backend.spl` (287), `nogc_async_mut/torch/backend.spl` (287), `gc_async_mut/torch/backend.spl` (292) | ~574 | Extract shared ops to `common/torch/backend_ops.spl` | P2 |
| D4 | **Backend MIR visitor pattern** | `cuda_backend.spl`, `wasm_backend.spl`, `c_backend_translate.spl` | ~450-600 | Extract `BackendVisitor` trait for shared walk logic | P2 |
| D5 | **hir_types.spl tag constants** | `10.frontend/core/hir_types.spl`, `20.hir/hir_types.spl` | ~200-400 | Extract shared constants to `00.common/hir_type_tags.spl` | P2 |
| D6 | **error.spl formatting overlap** | `00.common/error.spl`, `10.frontend/core/error.spl` | ~100 | Rename frontend version to `easyfix_errors.spl` | P2 |
| D7 | **const_keys.spl potential overlap** | `30.types/const_keys.spl` (38 fns), `35.semantics/const_keys.spl` (19 fns) | ~unknown | Verify if logic overlaps; extract shared helpers if so | P2 |
| D8 | **lower_to_hir_impl compat copy** | `80.driver/driver.spl` L398 (full) vs L493 (simplified 10-line copy) | ~10 | Delete simplified copy or migrate callers to full version | P1 |
| D9 | **WatBuilder emit repetition** | `wasm_backend.spl` L245-580: ~50 one-liner `emit_*` methods | ~200 | Table-driven approach or macro generation | P2 |

**Total duplicated/triplicated lines: ~3,300+**

---

## 7. Layer Violations -- Complete Catalog

### Upward violations (lower layer imports from higher layer)

| # | Source (Layer) | Target (Layer) | Import | Severity | Team | Fix |
|---|---------------|----------------|--------|----------|------|-----|
| LV1 | `00.common/compiler_services.spl` (L0) | `70.backend` (L7) | `compiler.backend.backend_port` | **CRITICAL** | T1 | Extract `BackendPort` to `00.common` |
| LV2 | `00.common/attributes.spl` (L0) | `10.frontend` (L1) | `compiler.frontend.parser_types` | **HIGH** | T1 | Extract needed types to `00.common` |
| LV3 | `00.common/attributes.spl` (L0) | `30.types` (L3) | `compiler.types.type_layout` | **HIGH** | T1 | Extract `LayoutAttr` to `00.common` |
| LV4 | `50.mir/mir_lowering_expr.spl` (L5) | `70.backend` (L7) | `compiler.backend.gpu_intrinsics` | **CRITICAL** | T3 | Move to `00.common` or `30.types` |
| LV5 | `70.backend/build_native_pipeline.spl` (L7) | `80.driver` (L8) | `compiler.driver.*` (3 imports) | **CRITICAL** | T3 | Move file to `80.driver` |
| LV6 | `70.backend/codegen.spl` (L7) | `99.loader` (L9.9) | `compiler.loader.jit_instantiator` | **CRITICAL** | T3 | Use dependency injection |
| LV7 | `70.backend/backend/jit_interpreter.spl` (L7) | `95.interp` (L9.5) | `compiler.interp.execution.mod` | **HIGH** | T3 | Extract tool-finding to `70.backend/tool_discovery.spl` |
| LV8 | `70.backend/backend/llvm_backend_tools.spl` (L7) | `95.interp` (L9.5) | `compiler.interp.interpreter.llvm.tools.*` | **HIGH** | T3 | Same: extract to `tool_discovery.spl` |
| LV9 | `70.backend/backend/wasm_backend.spl` (L7) | `95.interp` (L9.5) | `compiler.interp.interpreter.llvm.tools` | **HIGH** | T3 | Same |
| LV10 | `70.backend/linker/wasm_linker.spl` (L7) | `95.interp` (L9.5) | `compiler.interp.interpreter.llvm.tools` | **HIGH** | T3 | Same |
| LV11 | `30.types/type_infer/context.spl` (L3) | `35.semantics` (L3.5) | `compiler.semantics.narrowing.*` | **HIGH** | T2 | Move narrowing types to `30.types/` |
| LV12 | `30.types/type_infer/inference_expr_ops.spl` (L3) | `35.semantics` (L3.5) | `compiler.semantics.narrowing.*` | **HIGH** | T2 | Same |
| LV13 | `30.types/type_infer/inference_expr.spl` (L3) | `35.semantics` (L3.5) | `compiler.semantics.narrowing.*` | **HIGH** | T2 | Same |
| LV14 | `30.types/type_infer_types.spl` (L3) | `35.semantics` (L3.5) | `compiler.semantics.narrowing.*` | **HIGH** | T2 | Same |
| LV15 | `30.types/type_infer.spl` (L3) | `35.semantics` (L3.5) | `compiler.semantics.narrowing.*` | **HIGH** | T2 | Same |
| LV16 | `10.frontend/frontend.spl` (L1) | `90.tools` (L9) | `compiler.tools.desugar_async` | **HIGH** | T1 | Move `desugar_async` to `10.frontend/desugar/` |
| LV17 | `20.hir/inference/infer.spl` (L2) | `90.tools` (L9) | `compiler.tools.suffix_registry` | **HIGH** | T1 | Move `SuffixRegistry` to `00.common/` |
| LV18 | `80.driver/build/doc_warnings.spl` (L8) | `85.mdsoc` (L8.5) | `compiler.mdsoc.types/layer_checker` | **MEDIUM** | T4 | Acceptable (driver orchestrates) |
| LV19 | `80.driver/build/duplication.spl` (L8) | `90.tools` (L9) | `compiler.tools.duplicate_check.*` | **MEDIUM** | T4 | Define tool interfaces in `80.driver` |
| LV20 | `10.frontend/treesitter/outline_lexer.spl` (L1) | `15.blocks` (L1.5) | `compiler.blocks.blocks.registry` | **MEDIUM** | T1 | Acceptable (adjacent layers) |

### Systemic Patterns

1. **`00.common` is not a leaf layer.** 3 upward imports break the fundamental guarantee that `00.common` has zero dependencies on higher layers. This is the most architecturally damaging pattern.
2. **`70.backend` -> `95.interp` for tool discovery.** 4 files import interpreter utilities solely to find external tools (wat2wasm, wasm-ld, etc.). This is a misplaced concern -- tool-finding is infrastructure, not interpretation.
3. **`30.types` -> `35.semantics.narrowing`** is a single dependency replicated across 5 files. Moving one file (`narrowing.spl`) fixes all 5 violations.
4. **`80.driver` -> `85/90` is architecturally expected** for an orchestrator layer but could be improved with facades.

---

## 8. Coupling and Cohesion Hotspots

### Fan-Out Hotspots (Import Count)

| # | File | Imports | Team | Assessment |
|---|------|---------|------|------------|
| 1 | `src/app/io/mod.spl` | 67 | T6 | Re-export hub; monitor growth |
| 2 | `src/compiler/10.frontend/core/parser_expr.spl` | 62 | T1 | CRITICAL -- needs parser_prelude.spl |
| 3 | `src/compiler/10.frontend/core/parser_decls.spl` | 51 | T1 | HIGH -- same fix |
| 4 | `src/compiler/10.frontend/core/parser_stmts.spl` | 48 | T1 | HIGH -- same fix |
| 5 | `src/compiler/10.frontend/core/parser_primary.spl` | 41 | T1 | HIGH -- same fix |
| 6 | `src/compiler/10.frontend/core/parser.spl` | 39 | T1 | HIGH -- same fix |
| 7 | `src/compiler/10.frontend/core/lexer.spl` | 39 | T1 | Medium |
| 8 | `src/compiler/80.driver/driver.spl` | 27 | T4 | HIGH -- imports from 11 layers |
| 9 | `src/compiler/30.types/associated_types.spl` | 26 | T2 | Re-export hub (acceptable) |
| 10 | `src/compiler/80.driver/driver_api.spl` | 24 | T4 | Public API surface |

### Public API Surface Hotspots (>50 functions)

| # | File | Public Fns | Team |
|---|------|-----------|------|
| 1 | `src/lib/nogc_sync_mut/kafka/types.spl` | 151 | T5 |
| 2 | `src/lib/nogc_sync_mut/ffi/llvm.spl` | 142 | T5 |
| 3 | `src/lib/gc_async_mut/gpu.spl` | 120 (est) | T5 |
| 4 | `src/lib/nogc_sync_mut/ftp_utils.spl` | 105 | T5 |
| 5 | `src/lib/nogc_sync_mut/amqp_utils.spl` | 95 | T5 |
| 6 | `src/lib/nogc_sync_mut/src/tensor.spl` | 94 | T5 |
| 7 | `src/compiler/10.frontend/core/mir.spl` | 92 | T1 |
| 8 | `src/compiler/10.frontend/core/ast.spl` | 92 | T1 |
| 9 | `src/compiler/70.backend/backend/riscv32_asm.spl` | 73 | T3 |
| 10 | `src/compiler/10.frontend/core/ast_expr.spl` | 70 | T1 |
| 11 | `src/compiler/10.frontend/core/lexer.spl` | 69 | T1 |
| 12 | `src/app/cli/query_rich.spl` | 61 | T6 |

---

## 9. Big-O Anti-Patterns -- All Flags

### 9a. `list = list + [item]` Anti-Pattern (O(n^2) aggregate)

This is the **most widespread anti-pattern** across the codebase, found in all 6 regions:

| Region | Files Affected | Total Instances | Worst Offenders |
|--------|---------------|-----------------|-----------------|
| `src/compiler/40.mono/` | 1 | 3 | `engine.spl` -- monomorphization hot path |
| `src/compiler/90.tools/` | 8+ | ~20 | `detector.spl` -- duplicate detection |
| `src/compiler/70.backend/` | 4 | ~10 | `native/mod.spl` -- SMF header building |
| `src/lib/compression/` | 4 | ~8 | `inflate.spl`, `types.spl` -- decompression hot path |
| `src/lib/database/` | 3 | ~6 | `statement.spl`, `sqlite_ffi.spl` |
| `src/lib/kafka/` | 1 | 2 | `serialization.spl` -- serialization hot path |
| `src/app/mcp/` | 2 | 16 | `main_lazy_debug_tools.spl` (13), `main_lazy_tasks.spl` (3) |
| `src/lib/io/` | 3 | ~5 | `tcp.spl`, `debug_state.spl`, `sqlite_ffi.spl` |

**Total: ~70+ instances.** Fix: Replace all with `.push()`.

### 9b. O(n^2) String Concatenation in Loops

| File | Instances | Severity | Fix |
|------|-----------|----------|-----|
| `35.semantics/error_formatter.spl` | 70 | HIGH | Use `List<text>` + `.join("")` |
| `30.types/dim_constraints_types.spl:396-407` | 5 | MEDIUM | Same |
| `35.semantics/lint/remote_exec_lint.spl:327` | 1 | MEDIUM | Same |

### 9c. Nested Loop / Algorithm Issues

| File | Pattern | Severity |
|------|---------|----------|
| `10.frontend/core/parser_primary.spl:140+152` | `for 0..100000` containing `for 0..10000` = O(10^9) worst case | CRITICAL |
| `10.frontend/core/lexer_scanners.spl:205` | `for 0..1000000` single scan | HIGH |
| `src/lib/compression/types.spl:50-134` | O(n^3) Huffman tree (repeated linear min-find + list rebuild) | CRITICAL |
| `90.tools/duplicate_check/detector.spl:229-244` | Bubble sort O(n^2) | HIGH |
| `src/app/cli/query_rich.spl:111-116` | Nested loop dedup O(n*m) | MEDIUM |
| `70.backend/backend/mir_to_llvm.spl:78+84` | O(F*S) string_globals traversal per function | MEDIUM |

### 9d. `.contains()` on Lists (O(n) per call)

| File | Context | Fix |
|------|---------|-----|
| `30.types/type_infer/generalization.spl` | 5 instances on type var lists | Use Set |
| `70.backend/backend/common/isel_context.spl:95` | `frame_slots.contains()` in instruction selection | Use Dict |
| `src/lib/lazy/transform.spl:272` | Dedup via linear scan | Use Set |
| `src/lib/iterator/reduce.spl:390` | Group-by via linear scan | Use Dict |
| `10.frontend/core/call_graph.spl:290` | Path dedup | Use Set |
| `10.frontend/core/aop.spl:492,498` | Rules dedup | Use Set |

---

## 10. Per-Team Summary

### Team 1: Compiler Frontend (00.common, 10.frontend, 15.blocks, 20.hir)
181 files, ~49.9K lines. Four oversized files (1035, 930, 850, 811 lines). The most critical issue is `00.common` importing from higher layers, which breaks the foundational layering contract. The parser files have extreme fan-out (up to 62 imports) that would benefit from a shared prelude. The lexer and parser use `for i in 0..100000` idiom extensively as while-loop substitutes with excessively large bounds.

### Team 2: Compiler Middle (25.traits, 30.types, 35.semantics, 40.mono)
132 files, ~38.7K lines. No files exceed 800 lines, but two are at 798 and 779. The single architectural issue is `30.types` depending on `35.semantics.narrowing` (5 files, one fix). The monomorphization engine has O(n^2) list concat in a hot path. `error_formatter.spl` has 70 instances of string concatenation that should use list+join.

### Team 3: Compiler Backend (50.mir, 55.borrow, 60.mir_opt, 70.backend)
253 files, ~68K lines. One oversized file (`mir_to_llvm.spl` at 941 lines). The most serious issues are layer violations: `50.mir` importing from `70.backend`, and `70.backend` importing from `95.interp` (4 files) and `80.driver`. The backend has structural duplication across cuda/wasm/c backends that could be deduplicated via a `BackendVisitor` trait.

### Team 4: Compiler Driver (80.driver, 85.mdsoc, 90.tools, 95.interp, 99.loader)
451 files, ~64K lines. Three oversized files (974, 895, 785 lines). The confirmed byte-identical duplicate of `bootstrap_pipeline.spl` is the highest-value dedup target (785 lines). `driver.spl` has the highest coupling in the compiler (27 imports from 11 layers). The `list = list + [item]` anti-pattern is pervasive in `90.tools/` (~20 instances).

### Team 5: Standard Library (src/lib/)
1,546 files, ~355K lines (largest region). Four oversized files. The O(n^3) Huffman tree construction is the most severe algorithmic issue in the entire codebase. `easy_fix/rules.spl` monolith should be replaced by the already-existing split version. The torch backend is triplicated across three lib variants. `kafka/types.spl` at 151 functions has the highest API surface in the codebase.

### Team 6: Application Layer (src/app/)
479 files, ~95K lines. `query_rich.spl` at 2,421 lines is the single largest file in the entire codebase (3x the limit). It has a detailed 6-file split plan ready. The `bootstrap_pipeline.spl` duplicate was confirmed from this side as well. `io/mod.spl` at 67 imports is the highest fan-out file outside the compiler.

---

## 11. Recommended Execution Order

### Phase 1: Quick Wins (1-2 days, high ROI)

1. **Fix `list = list + [item]` globally.** This is a mechanical find-and-replace across ~70 sites. Start with hot paths: `compression/`, `kafka/serialization.spl`, `40.mono/engine.spl`. Use: `list.push(item)`.

2. **Delete duplicate `bootstrap_pipeline.spl`.** Pick canonical location, replace the other with a re-export. Zero risk, 785 lines removed.

3. **Retire `easy_fix/rules.spl` monolith.** The split version already exists in `common/tooling/easy_fix/`. Replace monolith with re-export.

### Phase 2: Critical Architecture (3-5 days)

4. **Fix `00.common` layer violations.** Extract `Attribute`, `Expr`, `LayoutAttr`, `BackendPort` types into `00.common/`. This unblocks clean compilation ordering.

5. **Move `narrowing.spl` types to `30.types/`.** Fixes 5 violations with one file move.

6. **Extract tool-finding from `95.interp` to `70.backend/tool_discovery.spl`.** Fixes 4 violations.

7. **Move `gpu_intrinsics.is_gpu_intrinsic()` to `00.common`.** Fixes `50.mir` -> `70.backend` violation.

### Phase 3: File Splits (1-2 weeks)

8. **Split `query_rich.spl` (2,421 lines).** Use the detailed 6-file plan from Team 6. This is the highest-impact single file split.

9. **Split `mir_to_llvm.spl`, `lint/main.spl`, `eval_ops.spl`, `driver.spl`.** All have natural split points identified. Target: all compiler files under 800 lines.

10. **Split stdlib oversized files:** `llvm.spl`, `gpu.spl`, `database.spl`. Section markers already exist.

### Phase 4: Performance and Dedup (ongoing)

11. **Fix string concat in `error_formatter.spl`** (70 instances) and `dim_constraints_types.spl`.

12. **Reduce parser fan-out** with `parser_prelude.spl`.

13. **Extract `BackendVisitor` trait** for shared MIR walk logic.

14. **Reduce loop bounds** in parser/lexer (`0..100000` -> `0..10000` for inner loops).

15. **Replace `.contains()` with Set/Dict** in identified hotspots.

---

*Report generated 2026-03-25 by consolidation of 6 team analyses.*
