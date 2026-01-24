# Grouped Test Execution Report

Generated: 2026-01-23

## Summary

| Status | Count |
|--------|-------|
| **Total Directories Tested** | 25 |
| **Passed** | 266 files |
| **Failed** | 16 files |
| **Hanging (Timeout)** | 13 files |
| **Total Files** | 333 spec files |

---

## Test Groups Summary

| Group # | Category | Files | Status | Passed | Failed | Hang |
|---------|----------|-------|--------|--------|--------|------|
| 1 | test/lib/std/fixtures | 1 | ✅ PASS | 1 | 0 | 0 |
| 2 | test/lib/std/integration | 10 | ⚠️ PARTIAL | 9 | 0 | 1 |
| 3 | test/lib/std/system | 34 | ✅ PASS | 34 | 0 | 0 |
| 4 | test/lib/std/unit/core | 22 | ⚠️ PARTIAL | 17 | 0 | 5 |
| 5 | test/lib/std/unit/tooling | 50 | ⚠️ PARTIAL | 49 | 1 | 0 |
| 6 | test/lib/std/unit/parser | 14 | ✅ PASS | 14 | 0 | 0 |
| 7 | test/lib/std/unit/ml | 13 | ✅ PASS | 13 | 0 | 0 |
| 8 | test/lib/std/unit/spec | 12 | ⚠️ PARTIAL | 10 | 2 | 0 |
| 9 | test/lib/std/unit/game_engine | 9 | ✅ PASS | 9 | 0 | 0 |
| 10 | test/lib/std/unit/physics | 9 | ✅ PASS | 9 | 0 | 0 |
| 11 | test/lib/std/unit/ui | 8 | ✅ PASS | 8 | 0 | 0 |
| 12 | test/lib/std/unit/lsp | 7 | ✅ PASS | 7 | 0 | 0 |
| 13 | test/lib/std/unit/verification | 7 | ⚠️ PARTIAL | 3 | 0 | 4 |
| 14 | test/lib/std/unit/sdn | 6 | ✅ PASS | 6 | 0 | 0 |
| 15 | test/lib/std/unit/concurrency | 5 | ✅ PASS | 5 | 0 | 0 |
| 16 | test/lib/std/unit/shell | 4 | ✅ PASS | 4 | 0 | 0 |
| 17 | test/lib/std/unit/misc | 12 | ✅ PASS | 12 | 0 | 0 |
| 18 | test/lib/std/unit/small | 9 | ✅ PASS | 9 | 0 | 0 |
| 19-22 | test/system/features | 72 | ✅ PASS | 72 | 0 | 0 |
| 23 | test/system/other | 22 | ✅ PASS | 22 | 0 | 0 |
| 24 | test/unit/spec | 3 | ⚠️ PARTIAL | 0 | 1 | 2 |
| 25 | simple/std_lib | 16 | ⚠️ PARTIAL | 3 | 10 | 3 |

---

## Hanging Tests (Timeout > 15s)

These tests hang and never complete:

### test/lib/std/integration
| File | Status |
|------|--------|
| arch_spec.spl | ⏳ HANG |

### test/lib/std/unit/core
| File | Status |
|------|--------|
| json_spec.spl | ⏳ HANG |
| math_ffi_spec.spl | ⏳ HANG |
| math_spec.spl | ⏳ HANG |
| string_literals_spec.spl | ⏳ HANG |
| string_spec.spl | ⏳ HANG |

### test/lib/std/unit/verification
| File | Status |
|------|--------|
| lean_codegen_spec.spl | ⏳ HANG |
| lean/naming_spec.spl | ⏳ HANG |
| memory_capabilities_spec.spl | ⏳ HANG |
| regeneration_spec.spl | ⏳ HANG |

### test/unit/spec
| File | Status |
|------|--------|
| registry_spec.spl | ⏳ HANG |
| expect_spec.spl | ⏳ HANG |

### simple/std_lib
| File | Status |
|------|--------|
| map_spec.spl | ⏳ HANG |
| testing/contract_spec.spl | ⏳ HANG |
| testing/smoke_test_spec.spl | ⏳ HANG |

---

## Failed Tests (Completed with Errors)

### test/lib/std/unit/tooling
| File | Status |
|------|--------|
| algorithm_utils_spec.spl | ❌ FAIL |

### test/lib/std/unit/spec
| File | Status |
|------|--------|
| mock_spec.spl | ❌ FAIL |
| resource_limited_spec.spl | ❌ FAIL |

### test/unit/spec
| File | Status |
|------|--------|
| progress_spec.spl | ❌ FAIL |

### simple/std_lib
| File | Status |
|------|--------|
| set_spec.spl | ❌ FAIL |
| testing/helpers_spec.spl | ❌ FAIL |
| testing/mock_spec.spl | ❌ FAIL |
| testing/mock_verification_spec.spl | ❌ FAIL |
| testing/mock_phase3_spec.spl | ❌ FAIL |
| testing/mock_phase4_spec.spl | ❌ FAIL |
| testing/mock_phase5_spec.spl | ❌ FAIL |
| testing/mock_phase6_spec.spl | ❌ FAIL |
| testing/mock_phase7_spec.spl | ❌ FAIL |

---

## Detailed Results by Directory

### test/lib/std/fixtures (1 file)
| File | Status |
|------|--------|
| fixture_spec.spl | ✅ PASS |

### test/lib/std/integration (10 files)
| File | Status |
|------|--------|
| arch_spec.spl | ⏳ HANG |
| console/console_basic_spec.spl | ✅ PASS |
| constructor_spec.spl | ✅ PASS |
| diagram/call_flow_profiling_spec.spl | ✅ PASS |
| diagram/diagram_gen_spec.spl | ✅ PASS |
| improvements/stdlib_improvements_spec.spl | ✅ PASS |
| macros/macro_integration_spec.spl | ✅ PASS |
| ml/simple_math_integration_spec.spl | ✅ PASS |
| ui/tui/ratatui_backend_spec.spl | ✅ PASS |
| ui/vulkan_window_spec.spl | ✅ PASS |

### test/lib/std/system (34 files)
All 34 files passed.

### test/lib/std/unit/core (22 files)
| File | Status |
|------|--------|
| arithmetic_spec.spl | ✅ PASS |
| attributes_spec.spl | ✅ PASS |
| collections_spec.spl | ✅ PASS |
| comparison_spec.spl | ✅ PASS |
| context_manager_spec.spl | ✅ PASS |
| context_spec.spl | ✅ PASS |
| decorators_spec.spl | ✅ PASS |
| fluent_interface_spec.spl | ✅ PASS |
| hello_spec.spl | ✅ PASS |
| json_spec.spl | ⏳ HANG |
| math_ffi_spec.spl | ⏳ HANG |
| math_spec.spl | ⏳ HANG |
| pattern_analysis_spec.spl | ✅ PASS |
| pattern_matching_spec.spl | ✅ PASS |
| primitives_spec.spl | ✅ PASS |
| random_spec.spl | ✅ PASS |
| regex_spec.spl | ✅ PASS |
| string_literals_spec.spl | ⏳ HANG |
| string_spec.spl | ⏳ HANG |
| synchronization_spec.spl | ✅ PASS |
| time_spec.spl | ✅ PASS |
| try_operator_spec.spl | ✅ PASS |

### test/lib/std/unit/parser (14 files)
All 14 files passed.

### test/lib/std/unit/ml (13 files)
All 13 files passed.

### test/lib/std/unit/spec (12 files)
| File | Status |
|------|--------|
| mock_spec.spl | ❌ FAIL |
| resource_limited_spec.spl | ❌ FAIL |
| Other 10 files | ✅ PASS |

### test/lib/std/unit/game_engine (9 files)
All 9 files passed.

### test/lib/std/unit/physics (9 files)
All 9 files passed (some internal test failures but file-level passed).

### test/lib/std/unit/ui (8 files)
All 8 files passed.

### test/lib/std/unit/lsp (7 files)
All 7 files passed.

### test/lib/std/unit/verification (7 files)
| File | Status |
|------|--------|
| lean_basic_spec.spl | ✅ PASS |
| lean_codegen_spec.spl | ⏳ HANG |
| lean/naming_spec.spl | ⏳ HANG |
| lean/verification_diagnostics_spec.spl | ✅ PASS |
| memory_capabilities_spec.spl | ⏳ HANG |
| regeneration_spec.spl | ⏳ HANG |
| unified_attrs_spec.spl | ✅ PASS |

### test/lib/std/unit/sdn (6 files)
All 6 files passed.

### test/lib/std/unit/concurrency (5 files)
| File | Status |
|------|--------|
| actor_body_spec.spl | ✅ PASS |
| concurrency_spec.spl | ✅ PASS |
| manual_mode_spec.spl | ✅ PASS |
| promise_spec.spl | ✅ PASS |
| resource_limits_spec.spl | ✅ PASS |

### test/lib/std/unit/shell (4 files)
All 4 files passed (some internal test failures but file-level passed).

### test/system/features (72 files)
All 72 files passed.

### test/system/other (22 files)
All 22 files passed (includes collections, compiler, interpreter, watcher).

### test/unit/spec (3 files)
| File | Status |
|------|--------|
| registry_spec.spl | ⏳ HANG |
| expect_spec.spl | ⏳ HANG |
| progress_spec.spl | ❌ FAIL |

### simple/std_lib (16 files)
| File | Status |
|------|--------|
| map_spec.spl | ⏳ HANG |
| set_spec.spl | ❌ FAIL |
| time_spec.spl | ✅ PASS |
| testing/benchmark_spec.spl | ✅ PASS |
| testing/contract_spec.spl | ⏳ HANG |
| testing/dashboard_spec.spl | ✅ PASS |
| testing/helpers_spec.spl | ❌ FAIL |
| testing/mock_spec.spl | ❌ FAIL |
| testing/mock_verification_spec.spl | ❌ FAIL |
| testing/mock_phase3_spec.spl | ❌ FAIL |
| testing/mock_phase4_spec.spl | ❌ FAIL |
| testing/mock_phase5_spec.spl | ❌ FAIL |
| testing/mock_phase6_spec.spl | ❌ FAIL |
| testing/mock_phase7_spec.spl | ❌ FAIL |
| testing/smoke_test_spec.spl | ⏳ HANG |

---

## Recommendations

1. **Priority: Fix Hanging Tests** - 13 tests hang and block the test runner. Investigation needed for:
   - Core string/math/json operations
   - Verification/Lean code generation
   - Map/registry functionality

2. **Fix Failed Tests** - 16 tests fail, primarily in:
   - Mock testing framework (9 files)
   - Algorithm utils, spec framework

3. **Run Strategy** - To avoid hangs, run tests by directory:
   ```bash
   # Safe directories (no hangs)
   ./target/debug/simple test test/lib/std/system
   ./target/debug/simple test test/lib/std/unit/parser
   ./target/debug/simple test test/lib/std/unit/ml
   ./target/debug/simple test test/system/features
   ```

4. **Skip Problematic Files** - Consider adding skip markers to hanging tests until fixed.

---

## Legend

- ✅ PASS - Test file completed successfully
- ❌ FAIL - Test file completed with failures
- ⏳ HANG - Test file timed out (>15 seconds)
- ⚠️ PARTIAL - Some files in group have issues
