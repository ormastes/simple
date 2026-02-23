# Test Failure Report

**Generated:** 2026-01-30
**Test Run:** Latest (484 test files)
**Total Tests:** 7,604
**Passed:** 6,886 (90.6%)
**Failed:** 718 (9.4%)
**Duration:** 75.33 seconds

---

## Executive Summary

The test suite shows **90.6% pass rate** with 718 failures across 484 test files. The failures cluster in 6 critical areas:

1. **Parser/Lexer Infrastructure** (148+ failures) - Foundational parsing issues
2. **Compiler Core** (148+ failures) - Lexer/linker failures blocking compilation
3. **LSP Server** (80 failures) - Language server integration broken
4. **ML/Torch Integration** (31 failures) - Deep learning features failing
5. **Database/Collections** (46 failures) - Core data structure issues
6. **Type System** (13+ failures) - Type inference/checking problems

**Critical Finding:** 50+ tests crash with "Process exited with code 1", indicating severe runtime failures beyond simple test assertions.

---

## Failure Distribution by Category

### 1. Parser/TreeSitter (148+ failures)

**Impact:** HIGH - Blocks parsing of new language features

| Test File | Failures | Duration | Status |
|-----------|----------|----------|--------|
| `parser_error_recovery_spec.spl` | 37 | 37ms | All failed |
| `parser_literals_spec.spl` | 4 | 46ms | Partial |
| `parser_control_flow_spec.spl` | 2 | 55ms | Partial |
| `parser_expressions_spec.spl` | 2 | 50ms | Partial |
| `parser_skip_keyword_spec.spl` | 1 | 20ms | **CRASH** |
| `parser_default_keyword_spec.spl` | 1 | 21ms | **CRASH** |
| `parser_static_keyword_spec.spl` | 1 | 17ms | **CRASH** |
| `treesitter_lexer_spec.spl` | 1 | 187ms | **CRASH** |
| `treesitter_incremental_spec.spl` | 1 | 176ms | **CRASH** |
| `treesitter_cursor_spec.spl` | 1 | 16ms | **CRASH** |
| `treesitter_error_recovery_spec.spl` | 1 | 20ms | **CRASH** |
| `treesitter_query_spec.spl` | 1 | 19ms | **CRASH** |
| `treesitter_tree_spec.spl` | 1 | 15ms | **CRASH** |

**Common Errors:**
- "Unexpected token: expected Fn, found Static"
- "Unexpected token: expected expression, found Default"
- "Unexpected token: expected identifier, found Newline"

**Root Cause:** New keywords (`skip`, `default`, `static`) not properly integrated into parser grammar.

---

### 2. Compiler Infrastructure (148+ failures)

**Impact:** CRITICAL - Blocks all compilation paths

| Test File | Failures | Duration | Status |
|-----------|----------|----------|--------|
| `lexer_spec.spl` | 128 | 96ms | **CATASTROPHIC** |
| `linker_spec.spl` | 18 | 39ms | All failed |
| `note_sdn_bdd_spec.spl` | 1 | 235ms | **CRASH** |
| `note_sdn_spec.spl` | 1 | 194ms | **CRASH** |
| `generic_template_spec.spl` | 1 | 18ms | **CRASH** |

**Common Errors:**
- Parse errors on basic lexer tokens
- Semantic errors: undefined identifiers
- Process crashes during compilation

**Root Cause:** Lexer regression or incomplete migration to new token types.

---

### 3. LSP/Language Server (80 failures)

**Impact:** HIGH - Blocks IDE integration and developer experience

| Test File | Failures | Duration | Status |
|-----------|----------|----------|--------|
| `message_dispatcher_spec.spl` | 29 | 618ms | All failed |
| `document_sync_spec.spl` | 18 | 566ms | All failed |
| `server_lifecycle_spec.spl` | 17 | 549ms | All failed |
| `completion_spec.spl` | 11 | 32ms | All failed |
| `references_spec.spl` | 5 | 27ms | All failed |

**Common Errors:**
- LSP protocol message handling failures
- Document synchronization issues
- Server lifecycle crashes

**Root Cause:** LSP server implementation incomplete or broken after recent changes.

---

### 4. ML/Torch Integration (31 failures, SLOW)

**Impact:** MEDIUM - Blocks deep learning features, but isolated

| Test File | Failures | Duration | Status |
|-----------|----------|----------|--------|
| `activation_spec.spl` | 6 | **1631ms** | All failed |
| `recurrent_spec.spl` | 4 | **1801ms** | Partial |
| `transformer_spec.spl` | 4 | **1618ms** | Partial |
| `fft_spec.spl` | 4 | **1399ms** | All failed |
| `linalg_spec.spl` | 3 | **1358ms** | Partial |
| `simple_math_spec.spl` | 3 | **1134ms** | All failed |
| `autograd_spec.spl` | 3 | **1456ms** | Partial |
| `custom_autograd_spec.spl` | 3 | **986ms** | All failed |
| `dict_config_spec.spl` | 1 | **3366ms** | Partial |

**Total ML Test Time:** ~14 seconds (18.6% of total test runtime for 0.4% of tests)

**Common Errors:**
- "Unexpected token: expected expression, found At" (matrix multiplication operator)
- Parse errors on `@` operator in tensor operations

**Root Cause:** Matrix multiplication operator (`@`) not properly lexed/parsed outside math blocks.

---

### 5. Database/Collections (46 failures)

**Impact:** HIGH - Core data structures broken

| Test File | Failures | Duration | Status |
|-----------|----------|----------|--------|
| `database_sync_spec.spl` | 24 | 52ms | Partial |
| `hashmap_basic_spec.spl` | 8 | 29ms | All failed |
| `hashset_basic_spec.spl` | 7 | 42ms | All failed |
| `btree_basic_spec.spl` | 7 | 46ms | All failed |

**Common Errors:**
- Basic HashMap/HashSet operations failing
- Database synchronization issues

**Root Cause:** Collection implementations incomplete or recently broken.

---

### 6. Type System (13+ failures)

**Impact:** HIGH - Type inference broken for common patterns

| Test File | Failures | Duration | Status |
|-----------|----------|----------|--------|
| `underscore_wildcard_spec.spl` | 7 | 31ms | All failed |
| `collections_spec.spl` | 6 | 67ms | Partial |
| `type_inference_spec.spl` | 1 | 47ms | Partial |
| `dyn_trait_spec.spl` | 1 | 22ms | **CRASH** |
| `transitive_mixin_spec.spl` | 1 | 21ms | **CRASH** |
| `type_checker_basic_spec.spl` | 1 | 16ms | **CRASH** |
| `dyn_trait_coverage_spec.spl` | 1 | 16ms | **CRASH** |

**Common Errors:**
- Underscore wildcard pattern not working
- Dynamic trait type checking failures
- Process crashes on type inference

**Root Cause:** Recent type inference changes incomplete.

---

## Additional Failure Categories

### 7. Core Library (32 failures)
- `random_spec.spl` - 12 failed (RNG implementation)
- `decorators_spec.spl` - 7 failed (decorator syntax)
- `time_spec.spl` - 7 failed (451ms, datetime operations)
- `pattern_analysis_spec.spl` - 3 failed

### 8. Effects/Contracts (21 failures)
- `effect_annotations_spec.spl` - 20 failed (effect system)
- `class_invariant_spec.spl` - 1 **CRASH**

### 9. Tensor/GPU (27 failures)
- `tensor_interface_spec.spl` - 19 failed (**5155ms** - VERY SLOW!)
- `gpu_kernels_spec.spl` - 8 failed

### 10. Tooling (45 failures)
- `regex_utils_spec.spl` - 20 failed
- `path_utils_spec.spl` - 8 failed
- `todo_parser_spec.spl`, `arg_parsing_spec.spl`, `command_dispatch_spec.spl` - various

### 11. Physics Engine (22 failures)
- `vector_spec.spl` - 5 failed
- `datetime_ffi_spec.spl` - 8 failed
- Multiple collision/dynamics specs - 1 each **CRASH**

### 12. Shell/FileSystem (37 failures)
- `path_spec.spl` - 23 failed (path operations broken)
- `process_spec.spl` - 12 failed (process spawning)
- `file_find_spec.spl` - 8 failed
- `env_spec.spl` - 6 failed
- `list_compact_spec.spl` - 8 failed

### 13. Verification/Lean (14 failures)
- `verification_diagnostics_spec.spl` - 11 failed
- `lean_basic_spec.spl` - 3 failed

### 14. Concurrency (7 failures)
- `concurrency_spec.spl` - 5 failed
- `resource_limits_spec.spl` - 2 failed

### 15. CLI/Commands (36 failures)
- `cli_spec.spl` - 11 failed + **TIMEOUT** (30s)
- `diagram_gen_spec.spl` - 9 failed

### 16. Test Framework Meta (15 failures)
- `failure_analysis_spec.spl` - 9 failed (1363ms)
- `let_memoization_spec.spl` - 5 failed
- `context_sharing_spec.spl` - 6 failed

### 17. Generator/Coroutines (8 failures)
- `generator_state_machine_codegen_spec.spl` - 8 failed

### 18. Structs (9 failures)
- `structs_spec.spl` - 2 failed
- `primitive_types_spec.spl` - 3 failed
- `classes_spec.spl` - 1 **CRASH**

---

## Error Type Analysis

### Parse Errors (~150+ failures)

**Most Common:**
```
Unexpected token: expected Fn, found Static
Unexpected token: expected expression, found Default
Unexpected token: expected expression, found At
Unexpected token: expected identifier, found Assign
Unexpected token: expected Comma, found Colon
Unexpected token: expected identifier, found Xor
```

**Pattern:** New keywords and operators not integrated into parser grammar:
- `static` keyword
- `default` keyword
- `skip` keyword
- `@` operator (matrix multiplication)
- `xor` keyword

### Process Crashes (~50+ failures)

**Error Message:** `Error: Process exited with code 1`

**Affected Tests:**
- All 6 TreeSitter specs
- All 3 parser keyword specs (`skip`, `default`, `static`)
- Multiple type checker specs
- Multiple physics specs
- Multiple compiler specs

**Pattern:** Tests crash before running any assertions, indicating:
1. Fatal compilation errors
2. Runtime initialization failures
3. Missing dependencies

### Semantic Errors (~100+ failures)

**Most Common:**
```
semantic: function `filter_internal_flags` not found
semantic: method `char_at` not found on type `array`
semantic: cannot modify self.features in immutable fn method
semantic: Undefined("undefined identifier: describe")
```

**Pattern:** API changes or incomplete implementations.

### Timeouts (5 failures)

**Affected Tests:**
- `cli_spec.spl` - 30s timeout (245ms before timeout)
- `spec_framework_spec.spl` - 30s timeout
- `fixture_spec.spl` - 30s timeout

**Pattern:** Infinite loops or blocking operations.

### Missing Files (~20 failures)

**Error:** `failed to read X: No such file or directory (os error 2)`

**Pattern:** Test files moved/deleted but still referenced in test database.

---

## Performance Issues

### Slowest Failing Tests

| Test | Duration | Failures | Impact |
|------|----------|----------|--------|
| `tensor_interface_spec.spl` | **5155ms** | 19 | Extremely slow |
| `dict_config_spec.spl` | **3366ms** | 1 | Very slow |
| `recurrent_spec.spl` | **1801ms** | 4 | Slow |
| `test_analysis_spec.spl` | **15993ms** | 26 | **CRITICAL - 21% of test time!** |
| `activation_spec.spl` | 1631ms | 6 | Slow |
| `transformer_spec.spl` | 1618ms | 4 | Slow |

**Total Time in Slow Failing Tests:** ~30 seconds (40% of total test runtime)

**Recommendation:** Mark slow tests with `slow_it` and run separately.

---

## Critical Blockers (Priority 0)

### 1. Lexer Catastrophic Failure
- **File:** `test/lib/std/unit/compiler/lexer_spec.spl`
- **Impact:** 128 failures (17.8% of all failures)
- **Status:** BLOCKING - Cannot lex basic syntax
- **Action:** Immediate investigation required

### 2. Parser Keyword Integration
- **Files:** All parser keyword specs
- **Impact:** New language features unusable
- **Keywords:** `skip`, `default`, `static`
- **Action:** Complete parser grammar integration

### 3. LSP Server Breakdown
- **Impact:** 80 failures, IDE integration broken
- **Action:** Fix message dispatcher and lifecycle

### 4. Collection Fundamentals
- **Impact:** HashMap, HashSet, BTree all failing
- **Action:** Fix core collection implementations

---

## High Priority (Priority 1)

1. **Type Inference Crashes** - 7 crashes in type checker
2. **TreeSitter Integration** - All 6 specs crashing
3. **Process Crashes** - 50+ tests crashing before assertions
4. **Matrix Operator** - `@` operator not parsing
5. **Shell Operations** - 37 failures in path/process/env

---

## Medium Priority (Priority 2)

1. **ML/Torch Integration** - 31 failures (but isolated)
2. **Effects System** - 20 failures in effect annotations
3. **Tooling Utilities** - 45 failures in regex/path/command utils
4. **Physics Engine** - 22 failures
5. **Verification** - 14 failures in Lean integration

---

## Low Priority (Priority 3)

1. **Performance Optimization** - Slow tests need `slow_it` markers
2. **Test Cleanup** - Remove references to deleted files
3. **Flaky Tests** - 56 tests with intermittent failures (per older report)
4. **Concurrency** - 7 failures
5. **Test Framework** - 15 meta-test failures

---

## Recommended Action Plan

### Phase 1: Stop the Bleeding (Days 1-3)

1. **Fix Lexer** - Restore lexer to working state (128 failures)
2. **Integrate Keywords** - Complete `skip`, `default`, `static` parsing
3. **Fix Collections** - Restore HashMap/HashSet/BTree (22 failures)
4. **Stop Process Crashes** - Investigate 50+ crashing tests

**Target:** Reduce failures from 718 to ~400 (44% reduction)

### Phase 2: Restore Core Features (Days 4-7)

1. **LSP Server** - Fix message dispatcher/lifecycle (80 failures)
2. **Type System** - Fix underscore wildcard and type inference (13 failures)
3. **TreeSitter** - Fix all 6 TreeSitter integration specs
4. **Shell Ops** - Fix path/process/env operations (37 failures)

**Target:** Reduce failures from ~400 to ~200 (50% reduction)

### Phase 3: Polish and Optimize (Days 8-14)

1. **ML/Torch** - Fix matrix operator and tensor operations (31 failures)
2. **Effects** - Complete effect system implementation (21 failures)
3. **Tooling** - Fix utility failures (45 failures)
4. **Performance** - Mark slow tests, optimize critical paths
5. **Cleanup** - Remove stale test references, fix flaky tests

**Target:** Reduce failures from ~200 to <100 (>85% pass rate → >98% pass rate)

---

## Regression Analysis

**Suspected Recent Changes Causing Failures:**

1. **Parser Grammar Changes** - Keywords not fully integrated
2. **Type Inference Refactor** - Multiple type system crashes
3. **Lexer Migration** - 128 lexer failures suggest incomplete migration
4. **Collection Refactor** - HashMap/HashSet/BTree all broken
5. **Operator Addition** - `@` operator not parsing, `xor` keyword issues

**Recommendation:** Review recent commits to parser, lexer, type system, and collections.

---

## Test Health Metrics

| Metric | Value | Status |
|--------|-------|--------|
| Pass Rate | 90.6% | ⚠️ **FAIR** |
| Total Tests | 7,604 | ✅ Good coverage |
| Failed Tests | 718 | ⚠️ High |
| Crashing Tests | 50+ | 🔴 **CRITICAL** |
| Slow Tests | 10+ | ⚠️ Needs optimization |
| Test Duration | 75.33s | ✅ Acceptable |
| Slowest Test | 15.99s | 🔴 **CRITICAL** |

**Overall Health:** ⚠️ **NEEDS IMMEDIATE ATTENTION**

---

## Appendix: Failed Test Files by Path

### test/system/features/
- classes/classes_spec.spl
- generator_state_machine_codegen/generator_state_machine_codegen_spec.spl
- gpu_kernels/gpu_kernels_spec.spl
- llvm_backend/llvm_backend_spec.spl
- macros/macro_validation_spec.spl
- pipeline_components/pipeline_components_spec.spl
- structs/structs_spec.spl
- type_inference/type_inference_spec.spl
- type_inference/dyn_trait_spec.spl
- type_inference/transitive_mixin_spec.spl
- database_synchronization/database_sync_spec.spl
- underscore_wildcard/underscore_wildcard_spec.spl
- primitive_types/primitive_types_spec.spl
- parser/* (9 specs failing)
- treesitter/* (6 specs failing)
- effects/effect_annotations_spec.spl
- contracts/class_invariant_spec.spl
- tensor_interface/tensor_interface_spec.spl
- collections_spec.spl
- fault_detection/fault_detection_spec.spl
- parser_edge_cases_spec.spl
- type_checker/* (2 specs failing)

### test/system/collections/
- hashmap_basic_spec.spl
- hashset_basic_spec.spl
- btree_basic_spec.spl

### test/lib/std/unit/
- core/* (6 specs failing)
- concurrency/* (2 specs failing)
- ui/vulkan_renderer_spec.spl
- sdn/lexer_spec.spl
- parser/* (7 specs failing)
- lsp/* (5 specs failing)
- lms/server_spec.spl
- mcp/failure_analysis_spec.spl
- ml/torch/* (9 specs failing)
- host/* (3 specs failing)
- physics/* (6 specs failing)
- tooling/* (11 specs failing)
- verification/* (2 specs failing)
- diagram/* (2 specs failing)
- infra/* (2 specs failing)
- shell/* (4 specs failing)
- fs/basic_spec.spl
- collections/list_compact_spec.spl
- interpreter/class_method_call_spec.spl
- spec/* (4 specs failing)
- hir/* (4 specs failing)
- compiler/* (4 specs failing)
- constructor_spec.spl
- cli_spec.spl
- todo_tests/todo_parser_spec.spl

### test/lib/std/system/
- sdn/file_io_spec.spl
- bugs/interpreter_bugs_spec.spl
- improvements/parser_improvements_spec.spl
- spec/matchers/spec_matchers_spec.spl

### test/lib/std/features/
- compiler/note_sdn_feature_spec.spl
- generic_bytecode_spec.spl

### test/lib/std/type_checker/
- type_inference_spec.spl
- type_inference_v2_spec.spl

### test/app/
- test_analysis_spec.spl

### test/unit/spec/
- registry_spec.spl

---

## Conclusion

The test suite has **718 failures (9.4%)** concentrated in 6 critical areas. The most severe issues are:

1. **Lexer catastrophic failure** (128 failures)
2. **50+ crashing tests** (process exit code 1)
3. **LSP server breakdown** (80 failures)
4. **Core collections broken** (22 failures)
5. **Parser keyword integration incomplete** (50+ parse errors)

**Immediate action required** on Phase 1 items to restore basic compiler functionality. Current state suggests recent refactoring broke foundational components.

**Estimated effort to reach 98% pass rate:** 2 weeks with focused effort on critical blockers.

**Next steps:**
1. Review recent commits to lexer, parser, type system
2. Roll back or complete incomplete migrations
3. Fix crashing tests (50+ process exit code 1)
4. Restore collection implementations
5. Complete keyword integration

---

**Report End**
