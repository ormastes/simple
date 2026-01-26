# Test Results

**Generated:** 2026-01-26 10:20:23
**Total Tests:** 406
**Status:** ⚠️ 30 FAILED

## Summary

| Status | Count | Percentage |
|--------|-------|-----------|
| ✅ Passed | 376 | 92.6% |
| ❌ Failed | 30 | 7.4% |
| ⏭️ Skipped | 0 | 0.0% |
| 🔕 Ignored | 0 | 0.0% |
| 🔐 Qualified Ignore | 0 | 0.0% |

---

## ❌ Failed Tests (30)

### 🔴 fixture_spec

**File:** `home/ormastes/dev/pub/simple/test/lib/std/fixtures/fixture_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-25T23:53:44.820840519+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test timed out after 30 seconds
Location: /home/ormastes/dev/pub/simple/test/lib/std/fixtures/fixture_spec.spl
```

---

### 🔴 test_pub_static_spec

**File:** `tmp/test_pub_static_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-26T09:54:30.663629655+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found Static
Location: /tmp/test_pub_static_spec.spl
```

---

### 🔴 context_managers_spec

**File:** `test/system/features/context_managers_spec.spl`
**Category:** System
**Failed:** 2026-01-25T07:10:22.702941107+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found Indent
Location: test/system/features/context_managers_spec.spl
```

---

### 🔴 hello_spec

**File:** `test/basic/hello_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-25T03:15:47.955872775+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
failed to read test/basic/hello_spec.spl: No such file or directory (os error 2)
Location: test/basic/hello_spec.spl
```

---

### 🔴 ui_dynamic_structure_spec

**File:** `test/system/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl`
**Category:** System
**Failed:** 2026-01-25T07:09:22.496279994+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Indent
Location: test/system/features/ui_dynamic_structure/ui_dynamic_structure_spec.spl
```

---

### 🔴 union_impl_spec

**File:** `test/lib/std/unit/spec/union_impl_spec.spl`
**Category:** Unit
**Failed:** 2026-01-25T07:37:09.069016677+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found String("\n    Simple union with two variants representing application status.\n    ")
Location: test/lib/std/unit/spec/union_impl_spec.spl
```

---

### 🔴 shared_pointers_spec

**File:** `test/system/features/shared_pointers/shared_pointers_spec.spl`
**Category:** System
**Failed:** 2026-01-26T10:19:06.257052997+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Shared
Location: test/system/features/shared_pointers/shared_pointers_spec.spl
```

---

### 🔴 arg_parsing_spec

**File:** `test/lib/std/unit/tooling/arg_parsing_spec.spl`
**Category:** Unit
**Failed:** 2026-01-25T07:25:13.218892275+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: method `char_at` not found on type `array`
Location: test/lib/std/unit/tooling/arg_parsing_spec.spl
```

---

### 🔴 pattern_matching_spec

**File:** `test/system/features/pattern_matching/pattern_matching_spec.spl`
**Category:** System
**Failed:** 2026-01-26T06:51:58.223043409+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found LParen
Location: test/system/features/pattern_matching/pattern_matching_spec.spl
```

---

### 🔴 single_line_functions_spec

**File:** `test/system/features/single_line_functions/single_line_functions_spec.spl`
**Category:** System
**Failed:** 2026-01-25T07:10:17.054416852+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found Assign
Location: test/system/features/single_line_functions/single_line_functions_spec.spl
```

---

### 🔴 static_fn_spec

**File:** `test/lib/std/unit/spec/static_fn_spec.spl`
**Category:** Unit
**Failed:** 2026-01-25T07:37:09.154301713+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found String("\n    Directional enum with optional magnitude.\n    ")
Location: test/lib/std/unit/spec/static_fn_spec.spl
```

---

### 🔴 ui_structural_patchset_spec

**File:** `test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl`
**Category:** System
**Failed:** 2026-01-25T07:09:22.600638314+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Indent
Location: test/system/features/ui_structural_patchset/ui_structural_patchset_spec.spl
```

---

### 🔴 resource_cleanup_spec

**File:** `src/lib/std/test/features/resource_cleanup_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-25T07:44:56.540595056+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Fn, found Colon
Location: src/lib/std/test/features/resource_cleanup_spec.spl
```

---

### 🔴 coverage_ffi_spec

**File:** `src/lib/std/test/unit/tooling/coverage_ffi_spec.spl`
**Category:** Unit
**Failed:** 2026-01-25T07:44:55.878021517+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: method `clear_coverage` not found on type `dict`
Location: src/lib/std/test/unit/tooling/coverage_ffi_spec.spl
```

---

### 🔴 contract_persistence_feature_spec

**File:** `src/lib/std/test/features/contract_persistence_feature_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-25T07:44:56.465935952+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Fn, found Colon
Location: src/lib/std/test/features/contract_persistence_feature_spec.spl
```

---

### 🔴 collections_spec

**File:** `test/system/interpreter/sample/python_inspired_sample/collections_spec.spl`
**Category:** System
**Failed:** 2026-01-25T07:03:17.678688278+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found For
Location: test/system/interpreter/sample/python_inspired_sample/collections_spec.spl
```

---

### 🔴 fuzz_spec

**File:** `src/lib/std/test/unit/testing/fuzz_spec.spl`
**Category:** Unit
**Failed:** 2026-01-25T07:44:15.689741624+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Val
Location: src/lib/std/test/unit/testing/fuzz_spec.spl
```

---

### 🔴 impl_blocks_spec

**File:** `test/system/features/impl_blocks/impl_blocks_spec.spl`
**Category:** System
**Failed:** 2026-01-25T07:07:41.668027292+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected RParen, found Colon
Location: test/system/features/impl_blocks/impl_blocks_spec.spl
```

---

### 🔴 pipeline_components_spec

**File:** `test/system/features/pipeline_components/pipeline_components_spec.spl`
**Category:** System
**Failed:** 2026-01-25T07:08:50.545608940+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected RParen, found Assign
Location: test/system/features/pipeline_components/pipeline_components_spec.spl
```

---

### 🔴 safe_unwrap_operators_spec

**File:** `test/system/features/safe_unwrap_operators/safe_unwrap_operators_spec.spl`
**Category:** System
**Failed:** 2026-01-25T07:10:17.112922188+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Indent
Location: test/system/features/safe_unwrap_operators/safe_unwrap_operators_spec.spl
```

---

### 🔴 optional_chaining_spec

**File:** `test/system/features/optional_chaining/optional_chaining_spec.spl`
**Category:** System
**Failed:** 2026-01-25T07:10:17.167254507+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found Assign
Location: test/system/features/optional_chaining/optional_chaining_spec.spl
```

---

### 🔴 type_aliases_spec

**File:** `test/system/features/type_aliases/type_aliases_spec.spl`
**Category:** System
**Failed:** 2026-01-25T07:09:14.836560916+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Indent
Location: test/system/features/type_aliases/type_aliases_spec.spl
```

---

### 🔴 sdoctest_spec

**File:** `test/system/features/sdoctest/sdoctest_spec.spl`
**Category:** System
**Failed:** 2026-01-25T07:08:50.596850216+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected indented block after ':', found Error("Unexpected character: '`'")
Location: test/system/features/sdoctest/sdoctest_spec.spl
```

---

### 🔴 bootstrap_spec

**File:** `simple/std_lib/test/features/bootstrap_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-26T00:09:33.161413837+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found And
Location: simple/std_lib/test/features/bootstrap_spec.spl
```

---

### 🔴 ui_ssr_hydration_spec

**File:** `test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl`
**Category:** System
**Failed:** 2026-01-25T07:09:22.550727349+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Indent
Location: test/system/features/ui_ssr_hydration/ui_ssr_hydration_spec.spl
```

---

### 🔴 arithmetic_spec

**File:** `test/system/features/arithmetic_spec.spl`
**Category:** System
**Failed:** 2026-01-25T07:10:22.758766021+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Plus
Location: test/system/features/arithmetic_spec.spl
```

---

### 🔴 lambdas_closures_spec

**File:** `test/system/features/lambdas_closures/lambdas_closures_spec.spl`
**Category:** System
**Failed:** 2026-01-25T07:07:48.353056458+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Colon
Location: test/system/features/lambdas_closures/lambdas_closures_spec.spl
```

---

### 🔴 indentation_blocks_spec

**File:** `test/system/features/indentation_blocks/indentation_blocks_spec.spl`
**Category:** System
**Failed:** 2026-01-25T07:07:41.729196669+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Newline
Location: test/system/features/indentation_blocks/indentation_blocks_spec.spl
```

---

### 🔴 capture_buffer_vreg_remapping_spec

**File:** `test/system/features/capture_buffer_vreg_remapping/capture_buffer_vreg_remapping_spec.spl`
**Category:** System
**Failed:** 2026-01-25T07:04:47.220792937+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found LParen
Location: test/system/features/capture_buffer_vreg_remapping/capture_buffer_vreg_remapping_spec.spl
```

---

### 🔴 test_comprehension_spec

**File:** `tmp/test_comprehension_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-26T09:57:53.104504678+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found For
Location: /tmp/test_comprehension_spec.spl
```

---

---

## 📊 Timing Analysis

---

## 🎯 Action Items

### Priority 1: Fix Failing Tests (30)

1. **fixture_spec** - Test timed out after 30 seconds
2. **test_pub_static_spec** - parse error: Unexpected token: expected identifier, found Static
3. **context_managers_spec** - parse error: Unexpected token: expected identifier, found Indent
4. **hello_spec** - failed to read test/basic/hello_spec.spl: No such file or directory (os error 2)
5. **ui_dynamic_structure_spec** - parse error: Unexpected token: expected expression, found Indent

### Priority 3: Stabilize Flaky Tests (8)

Tests with intermittent failures:
- hm_type_inference_spec (83.3% failure rate)
- helpers_spec (20.0% failure rate)
- classes_spec (20.0% failure rate)
- class_invariant_spec (50.0% failure rate)
- loops_spec (60.0% failure rate)

