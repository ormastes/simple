# Large File Refactoring Analysis (>800 lines)

**Date:** 2026-02-24
**Scope:** All `.spl` files in `src/` exceeding 800 lines
**Total files found:** 21 (including 3 identical torch/dyn_ffi copies)

---

## Summary

| Category | Count | Total Lines |
|----------|-------|-------------|
| CANNOT_REFACTOR | 9 | 9,277 |
| REFACTORABLE | 12 | 13,386 |

---

## CANNOT_REFACTOR Files

These files are monolithic by necessity. Splitting them would break algorithmic correctness, destroy phase cohesion, or provide no meaningful benefit.

### 1. `src/compiler/30.types/higher_rank_poly.spl` — 1632 lines

**Reason:** Tightly coupled 4-phase type system (Phases 5A-5D).

- Kind system, TypeVar, Quantifiers, HirType, PolyType, TypeScheme, QuantifierLevel, ScopeTracker, QuantifierContext, Substitution, HigherRankUnifier — all form a strict dependency chain
- 30 tests form a progressive narrative across 4 phases; splitting scatters test coverage
- Unification algorithm touches all type variants simultaneously
- Deliberately consolidated from phases 5A-5D; splitting loses pedagogical structure

### 2. `src/compiler/30.types/associated_types.spl` — 1539 lines

**Reason:** 4-phase system (Phases 4A-4D) with strict inter-phase dependencies.

- Phase 4A (definitions) → 4B (implementations) → 4C (projection/resolution) → 4D (solver integration)
- Unified HirType enum shared across all phases must evolve together
- TraitSolverEx depends on ALL prior phases; splitting breaks dependency flow
- 31 tests organized by phase validate the progression

### 3. `src/compiler/30.types/variance.spl` — 1490 lines

**Reason:** Monolithic inference algorithm that cannot be meaningfully split.

- `VarianceInference::infer()` is a 143-line recursive algorithm matching ALL HirType variants simultaneously
- Variance composition rules (flip, compose, combine) used throughout inference and checking
- Phase 6A (representation) → 6B (inference) → 6C (checking) with strict dependencies
- 27 tests validate phase progression

### 4. `src/lib/nogc_sync_mut/database/test_extended/database.spl` — 900 lines

**Reason:** Single monolithic class (TestDatabaseExtended) with shared mutable state.

- 40+ methods all operate on shared state (self.db, self.interner, next_*_id counters)
- Circular dependencies between helpers (update_test_result → update_counter → update_timing → add_timing_run)
- Query methods depend on core get_or_create_* methods called throughout
- Splitting requires passing db/interner everywhere — ORM-style pattern by design

### 5-7. `src/lib/*/torch/dyn_ffi.spl` — 882 lines each (x3 identical copies)

**Files:**
- `src/lib/nogc_sync_mut/torch/dyn_ffi.spl`
- `src/lib/nogc_async_mut/torch/dyn_ffi.spl`
- `src/lib/gc_async_mut/torch/dyn_ffi.spl`

**Reason:** Pure FFI translation layer — each function is a thin 2-3 line wrapper.

- 140+ wrapper functions calling `_call0`/`_call1`/`_call2`/`_call3`/`_call_n`
- No shared state or internal logic; purely mechanical translation
- 80+ export statements at the end; splitting requires re-exporting from parent module
- Splitting creates artificial module boundaries with no functional benefit
- **Note:** All 3 files are byte-identical copies across lib categories. Deduplication via shared base module is a separate concern from splitting.

### 8. `src/compiler/10.frontend/core/lexer.spl` — 851 lines

**Reason:** Monolithic finite state machine with 16 interdependent state variables.

- State variables (`lex_pos`, `lex_line`, `lex_col`, `lex_indent_stack`, `lex_pending_dedents`, `lex_round_paren_depth`, etc.) are synchronized during `lex_advance()`
- `lex_scan_token()` is a 310-line central dispatcher that branches to specialized scanners (_scan_number, _scan_string, _scan_ident)
- Context-dependent behavior: `lex_round_paren_depth` suppresses indentation tokens inside parentheses
- Maps 1:1 to a lexer specification; splitting breaks the natural automaton flow

### 9. `src/compiler/10.frontend/core/interpreter/eval_stmts.spl` — 836 lines

**Reason:** Global execution state shared across 20+ functions with phase-locked evaluation.

- Global flags manage execution flow: `eval_returning` + `eval_return_value`, `eval_breaking` + `eval_break_label`, `eval_had_error`
- Cascading scope management: `eval_stmt_if()`, `eval_stmt_for()`, `eval_stmt_match()` all call `env_push_scope()`/`env_pop_scope()` in paired semantics
- `eval_module()` has 5 ordered phases (register → declare → init → main → teardown) that depend on state from previous phases
- Threading state as parameters would destroy function signatures

---

## REFACTORABLE Files

These files have clear logical boundaries, minimal coupling between sections, and would benefit from splitting.

### 1. `src/app/mcp/main_lazy.spl` — 2131 lines → ~7 files

**Structure:** 34 inline tool handlers across 5-6 categories.

| Proposed Module | Contents | Est. Lines |
|----------------|----------|------------|
| `json_helpers.spl` | Escape, construction, parsing helpers | ~100 |
| `protocol_io.spl` | Read/write, initialize, tools list | ~150 |
| `diagnostic_tools.spl` | simple_read, simple_check, simple_symbols, simple_status, simple_edit, simple_multi_edit, simple_run | ~400 |
| `vcs_tools.spl` | simple_diff, simple_log, simple_squash, simple_new | ~200 |
| `api_search_tool.spl` | simple_api | ~150 |
| `debug_tools_lazy.spl` | 19 debug session/breakpoint/variable handlers | ~600 |
| `debug_log_tools_lazy.spl` | 6 debug logging handlers | ~200 |
| `main_lazy.spl` | Entry point + dispatcher | ~100 |

### 2. `src/compiler/30.types/simd.spl` — 1532 lines → ~2 files

| Proposed Module | Contents | Est. Lines |
|----------------|----------|------------|
| `simd_vector_types.spl` | Vec2f, Vec4f, Vec8f, Vec2d, Vec4d definitions and operations | ~400 |
| `simd_platform.spl` | SimdPlatform, SimdCapabilities, SimdIntrinsics, CPU feature detection | ~200 |
| Tests distributed or unified | | ~700 |

### 3. `src/compiler/30.types/macro_checker.spl` — 1218 lines → ~3 files

| Proposed Module | Contents | Est. Lines |
|----------------|----------|------------|
| `macro_def.spl` | MacroParam, MacroDef, MacroRegistry (Phase 7A) | ~200 |
| `macro_checker.spl` | MacroCall, TypeEnv, MacroTypeChecker, MacroTypeError (Phase 7B) | ~180 |
| `macro_expander.spl` | SubstitutionMap, MacroExpander (Phase 7C) | ~160 |

### 4. `src/compiler/30.types/const_keys.spl` — 1124 lines → ~3 files

| Proposed Module | Contents | Est. Lines |
|----------------|----------|------------|
| `key_extractor.spl` | KeyExtractor, ConstKeySet (Phase 8A) | ~150 |
| `const_key_type.spl` | HirType extensions, TemplateTypeInference (Phase 8B) | ~180 |
| `const_key_validator.spl` | KeyError, ConstKeyValidator, helpers (Phase 8C) | ~150 |

### 5. `src/compiler/30.types/bidirectional_checking.spl` — 1103 lines → ~4 files

| Proposed Module | Contents | Est. Lines |
|----------------|----------|------------|
| `bidirectional_types.spl` | HirType, HirExprKind, HirExpr, HirFunction, InferMode, Symbol types | ~200 |
| `bidirectional_inferencer.spl` | TypeInferencer class with all inference methods | ~300 |
| `bidirectional_tests.spl` | All 40 test functions organized by phase | ~400 |
| `bidirectional_main.spl` | main() entry point and exports | ~100 |

### 6. `src/app/dap/server.spl` — 1044 lines → ~4 files

| Proposed Module | Contents | Est. Lines |
|----------------|----------|------------|
| `dap_types.spl` | LaunchConfig, DebugContext, StackEntry, VariableInfo, DebuggerState, StepMode | ~200 |
| `dap_handlers.spl` | Handler methods by category (init, breakpoints, threads, variables, stepping) | ~450 |
| `dap_execution.spl` | execute_until_stop, execute_step, check_runtime_data_breakpoints | ~200 |
| `dap_server.spl` | DapServer class skeleton and main run loop | ~150 |

### 7. `src/app/test_runner_new/test_runner_main.spl` — 1038 lines → ~4 files

| Proposed Module | Contents | Est. Lines |
|----------------|----------|------------|
| `test_runner_core.spl` | run_tests(), run_single_test(), mode_to_str() | ~350 |
| `test_runner_modes.spl` | Mode dispatch (interpreter/smf/native/safe/composite) | ~250 |
| `test_runner_config.spl` | propagate_env_vars(), run_spl_doctest_mode(), run_combined_mode() | ~150 |
| `test_runner_main.spl` | CLI entry, memory tracking, argument parsing, main() | ~200 |

### 8. `src/compiler/70.backend/backend/c_backend.spl` — 979 lines → ~5 files

| Proposed Module | Contents | Est. Lines |
|----------------|----------|------------|
| `mir_to_c_types.spl` | Type mapping, local management, stack slot helpers | ~150 |
| `mir_to_c_instructions.spl` | translate_const, translate_binop, translate_call, etc. | ~300 |
| `mir_to_c_control_flow.spl` | translate_block, translate_terminator | ~150 |
| `mir_to_c_backend.spl` | MirTextCodegen trait stubs, header generation, CCodegenBackend | ~200 |
| `mir_to_c_main.spl` | MirToC class, translate_module, exports | ~100 |

### 9. `src/app/test_runner_new/test_runner_execute.spl` — 892 lines → ~6 files

| Proposed Module | Contents | Est. Lines |
|----------------|----------|------------|
| `test_executor_binary.spl` | find_simple_binary, find_runtime_lib_dir | ~100 |
| `test_executor_parsing.spl` | parse_test_output, extract_error_message, extract_number_* | ~150 |
| `test_executor_modes.spl` | run_test_file_interpreter, _smf, _native, _safe_mode | ~250 |
| `test_executor_coverage.spl` | build_coverage_wrapper, extract_coverage_sdn | ~100 |
| `test_executor_composite.spl` | composite, baremetal, remote, QEMU support | ~200 |
| `test_executor_main.spl` | make_result_from_output, list_tests_static, exports | ~100 |

### 10. `src/app/io/cli_ops.spl` — 848 lines → ~6 files

| Proposed Module | Contents | Est. Lines |
|----------------|----------|------------|
| `cli_helpers.spl` | Platform detection, process execution, file operations | ~70 |
| `cli_commands.spl` | run_code, run_file, run_repl, watch, run_tests | ~140 |
| `cli_tools.spl` | lint, fmt, fix, verify, migrate, query, diff, mcp, lsp | ~170 |
| `cli_compile.spl` | Main compile() argument parsing + delegation | ~200 |
| `cli_compile_backends.spl` | compile_baremetal, compile_c_backend, compile_vhdl | ~200 |
| `cli_ops.spl` | Entry point, stubs, centralized exports | ~70 |

### 11. `src/app/mcp/debug_tools.spl` — 829 lines → ~4 files

| Proposed Module | Contents | Est. Lines |
|----------------|----------|------------|
| `debug_schemas.spl` | All 19 schema_debug_* functions | ~250 |
| `debug_handlers.spl` | All 19 handle_debug_* functions | ~400 |
| `debug_tools.spl` | Imports, exports, re-exports | ~50 |

### 12. `src/compiler/85.mdsoc/mdsoc/types.spl` — 820 lines → TBD

Needs deeper analysis for specific split proposal.

---

## Notes

- **Torch FFI deduplication**: The three identical `torch/dyn_ffi.spl` files (882 lines each) could share a single base module rather than being fully duplicated. This is a deduplication concern, not a splitting concern.
- **Test co-location**: Several refactorable files contain inline tests. These can either stay with their module or be extracted to separate test files.
- **Phase-based files**: The compiler/30.types/ files follow a deliberate phase consolidation pattern. Files marked CANNOT_REFACTOR were intentionally designed as monolithic phase progressions.
