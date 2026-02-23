# Files Over 800 Lines - Refactoring Analysis
**Date**: 2026-01-31
**Status**: Analysis Complete

---

## Executive Summary

Found **19 active .spl files over 800 lines** (excluding .disabled and tests).

**Classification**:
- **Cannot refactor (impl block constraint)**: 4 files (4,870 lines total)
- **Can refactor**: 15 files (13,290 lines total)
- **Total**: 19 files (18,160 lines)

---

## Files That CANNOT Be Easily Refactored

These files are single large `impl` blocks. Simple language doesn't support splitting impl blocks across files.

| File | Lines | Constraint |
|------|-------|------------|
| `simple/compiler/parser.spl` | 1809 | Parser impl (76 methods) |
| `simple/compiler/type_infer.spl` | 1478 | HmInferContext impl (38 methods) |
| `simple/compiler/treesitter.spl` | 1333 | TreeSitter impl |
| `simple/compiler/lexer.spl` | 1250 | Lexer impl + helpers |
| **Total** | **4870** | **Language limitation** |

**Recommendation**: Document as technical debt. Wait for language support for split impl blocks, or extract standalone helper functions (modest 5-10% reduction).

---

## Files That CAN Be Refactored

These files have standalone functions, multiple types, or clear module boundaries.

### Priority 1: Application Files (Good Refactoring Candidates)

| File | Lines | Structure | Refactoring Potential |
|------|-------|-----------|----------------------|
| `test_runner_new/main.spl` | 1052 | 30+ standalone functions | ✅ **HIGH** - Split into types, args, files, execute, output, db, main |
| `simple/compiler/hir_lowering.spl` | 1148 | Types + HirLowering impl | ⚠️ Medium - Extract types, keep impl |

### Priority 2: I18n Files (Data Files)

| File | Lines | Structure | Refactoring Potential |
|------|-------|-----------|----------------------|
| `src/i18n/__init__.spl` | 1355 | Constant definitions by category | ✅ HIGH - Split by error category (parser/semantic/codegen/runtime) |
| `src/i18n/__init__.ko.spl` | 1355 | Korean translations (mirrors __init__.spl) | ✅ HIGH - Same structure as __init__.spl |
| `src/i18n/compiler.spl` | 1250 | Error code mappings | ⚠️ Medium - References __init__.spl constants |

**Note**: i18n files are interconnected. Refactoring requires coordinated changes.

### Priority 3: Tooling/Library Files

| File | Lines | Type | Refactoring Potential |
|------|-------|------|----------------------|
| `tooling/deployment/packaging.spl` | 1249 | Tooling | ✅ High - Likely has separable functions |
| `host/common/net/types.spl` | 1242 | Type definitions | ✅ High - Pure types, easy to split |
| `mcp/advanced.spl` | 1219 | MCP features | ✅ Medium - May have logical sections |
| `tooling/core/dependency.spl` | 1200 | Dependency mgmt | ✅ Medium - Likely has separable modules |
| `tooling/core/project.spl` | 1055 | Project mgmt | ✅ Medium - Likely has separable modules |

### Priority 4: Smaller Files (800-1000 lines)

| File | Lines | Type | Refactoring Potential |
|------|-------|------|----------------------|
| `mcp/multi_lang/rust.spl` | 978 | Multi-lang support | ⚠️ Medium |
| `verification/models/tensor_dimensions.spl` | 957 | Verification | ⚠️ Medium |
| `tooling/compiler/build_system.spl` | 944 | Build system | ✅ Medium |
| `tooling/core/errors.spl` | 931 | Error handling | ✅ Medium |
| `host/common/io/term_style.spl` | 918 | Terminal styling | ⚠️ Low - Close to target |

---

## Refactoring Strategy

### Approach 1: High-Impact Files (Recommended)

**Target**: 3-5 most impactful files
**Effort**: 2-4 hours
**Impact**: Eliminate ~5,000 lines in large files

Files to refactor:
1. ✅ **test_runner_new/main.spl** (1052 → ~150 lines) - Already started
2. **src/i18n/__init__.spl** (1355 → ~300 max) - Split by error category
3. **src/i18n/__init__.ko.spl** (1355 → ~300 max) - Mirror __init__.spl structure
4. **tooling/deployment/packaging.spl** (1249 → ~400 max) - TBD structure
5. **host/common/net/types.spl** (1242 → ~400 max) - Split type groups

### Approach 2: Complete Refactoring (Comprehensive)

**Target**: All 15 refactorable files
**Effort**: 8-12 hours
**Impact**: Eliminate ~13,000 lines in large files

All files from "CAN Be Refactored" list above.

### Approach 3: Conservative (Current)

**Target**: Already completed Phase 2.0
**Effort**: Complete
**Impact**: Eliminated 3 files >1400 lines (4,718 → max 825)

**Status**: ✅ COMPLETE
- mocking.spl: 1905 → 825 max
- regex.spl: 1408 → 561 max
- ast_convert.spl: 1405 → 577 max

---

## test_runner_new Refactoring Plan (IN PROGRESS)

**Current**: 1052 lines, single file

**Target modules**:
1. **test_runner_types.spl** (~140 lines) - ✅ CREATED
   - TestExecutionMode, TestLevel, OutputFormat
   - TestOptions, TestFileResult, TestRunResult, SkipFeatureInfo
   - FFI extern declarations

2. **test_runner_args.spl** (~130 lines) - TODO
   - parse_mode_str, parse_test_args

3. **test_runner_files.spl** (~200 lines) - TODO
   - File discovery: is_test_file, matches_level, discover_test_files
   - File utilities: read_file_content, file_has_*, shuffle_files
   - Feature tracking: extract_skip_feature_info, print_skip_features

4. **test_runner_execute.spl** (~350 lines) - TODO
   - Test execution: run_test_file_* (interpreter, smf, native)
   - Preprocessing: preprocess_sspec_file
   - Output parsing: parse_test_output, make_result_from_output
   - Binary finding: find_simple_new_binary, find_runtime_lib_dir

5. **test_runner_output.spl** (~100 lines) - TODO
   - Output formatting: print_result_*, print_summary, print_discovery_summary

6. **test_runner_db.spl** (~150 lines) - TODO
   - Database operations: write_test_db_run, atomic_update_file_test_db
   - File locking: acquire_file_lock

7. **main.spl** (~100 lines) - TODO
   - Main orchestration: run_tests, run_single_test, propagate_env_vars
   - Entry point: main()
   - Re-exports from all modules

**Result**: 1052 lines → 7 files, max 350 lines per file

---

## i18n Files Refactoring Plan

**Files**: `__init__.spl` (1355 lines), `__init__.ko.spl` (1355 lines)

**Target modules** (for both .spl and .ko.spl):
1. **src/i18n/common.spl** (~40 lines) - ✅ CREATED (partial)
   - Severity levels
   - Common error messages/labels/help

2. **src/i18n/parser.spl** (~200 lines) - TODO
   - Parser errors E0001-E0016
   - Titles, messages, labels, help, notes

3. **src/i18n/semantic.spl** (~700 lines) - TODO
   - Semantic errors E1001-E1A06
   - Control flow, capability, macro, AOP, custom blocks, mixins, SDN, DI, architecture rules

4. **src/i18n/codegen.spl** (~200 lines) - TODO
   - Codegen errors E2001-E2009

5. **src/i18n/runtime.spl** (~300 lines) - TODO
   - Runtime errors E3001-E3009, E4xxx, E5xxx, E6xxx

6. **src/i18n/verification.spl** (~200 lines) - TODO
   - Verification errors V-AOP-xxx, V-MACRO-xxx, V-TERM-xxx

7. **src/i18n/lint.spl** (~100 lines) - TODO
   - Lint messages

8. **src/i18n/explanations.spl** (~200 lines) - TODO
   - Error explanations for various codes

9. **__init__.spl** (~40 lines) - Re-export module
   - Import and re-export all categories

**Coordination needed**: `src/i18n/compiler.spl` (1250 lines) references these constants.

---

## Summary

| Category | Files | Lines | Status |
|----------|-------|-------|--------|
| **Phase 2.0 Complete** | 3 | 4,718 → 1,963 | ✅ DONE |
| **Cannot Refactor** | 4 | 4,870 | ⚠️ Language limitation |
| **Can Refactor - Priority 1** | 2 | 2,200 | 🔄 In Progress (1/2) |
| **Can Refactor - Priority 2** | 3 | 3,960 | ⏳ Planned |
| **Can Refactor - Priority 3** | 5 | 5,965 | ⏳ Planned |
| **Can Refactor - Priority 4** | 5 | 4,728 | ⏳ Optional |
| **Total** | 19 | 18,160 | - |

**Next Steps**:
1. Complete test_runner_new refactoring (6 more modules)
2. Refactor i18n files (coordinated split)
3. Tackle Priority 3 tooling files
4. Evaluate Priority 4 (already close to target)

---

## Recommendations

**Option A - Quick Win (Recommended)**:
- ✅ Complete test_runner_new (already started)
- Skip i18n (complex interconnections)
- Document impl block files as technical debt
- **Result**: 1 file refactored, ~900 lines saved

**Option B - High Impact**:
- Complete test_runner_new
- Refactor i18n files (coordinated effort)
- **Result**: 4 files refactored, ~4,000 lines saved

**Option C - Comprehensive**:
- Complete all 15 refactorable files
- **Result**: 15 files refactored, ~13,000 lines saved
- **Effort**: 8-12 hours

**Current recommendation**: Option A (quick win) + document the rest.
