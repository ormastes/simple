# Test Results

**Generated:** 2026-01-25 03:42:02
**Total Tests:** 92
**Status:** ⚠️ 5 FAILED

## Summary

| Status | Count | Percentage |
|--------|-------|-----------|
| ✅ Passed | 87 | 94.6% |
| ❌ Failed | 5 | 5.4% |
| ⏭️ Skipped | 0 | 0.0% |
| 🔕 Ignored | 0 | 0.0% |
| 🔐 Qualified Ignore | 0 | 0.0% |

---

## ❌ Failed Tests (5)

### 🔴 progress_spec

**File:** `test/unit/spec/progress_spec.spl`
**Category:** Unit
**Failed:** 2026-01-25T03:39:34.205414845+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected fn, struct, class, enum, union, impl, mod, extern, or pub after attributes, found String("\nUnit tests for test progress reporting functionality.\n\nThis test file verifies the progress reporting API used during long-running tests:\n- Basic progress message output with timestamps\n- Percentage and step-based completion reporting\n- Progress formatting and string interpolation\n- Integration with slow tests and error scenarios\n\nThe progress function provides visibility into test execution for debugging and monitoring.\n")
Location: test/unit/spec/progress_spec.spl
```

---

### 🔴 collections_spec

**File:** `test/system/interpreter/sample/python_inspired_sample/collections_spec.spl`
**Category:** System
**Failed:** 2026-01-25T03:40:06.332141820+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found For
Location: test/system/interpreter/sample/python_inspired_sample/collections_spec.spl
```

---

### 🔴 capture_buffer_vreg_remapping_spec

**File:** `test/system/features/capture_buffer_vreg_remapping/capture_buffer_vreg_remapping_spec.spl`
**Category:** System
**Failed:** 2026-01-25T03:41:35.633306816+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found LParen
Location: test/system/features/capture_buffer_vreg_remapping/capture_buffer_vreg_remapping_spec.spl
```

---

### 🔴 collections_spec

**File:** `test/system/compiler/sample/python_inspired_sample/collections_spec.spl`
**Category:** System
**Failed:** 2026-01-25T03:40:34.945715478+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found For
Location: test/system/compiler/sample/python_inspired_sample/collections_spec.spl
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

---

## 📊 Timing Analysis

---

## 🎯 Action Items

### Priority 1: Fix Failing Tests (5)

1. **progress_spec** - parse error: Unexpected token: expected fn, struct, class, enum, union, impl, mod, extern, or pub after attributes, found String("\nUnit tests for test progress reporting functionality.\n\nThis test file verifies the progress reporting API used during long-running tests:\n- Basic progress message output with timestamps\n- Percentage and step-based completion reporting\n- Progress formatting and string interpolation\n- Integration with slow tests and error scenarios\n\nThe progress function provides visibility into test execution for debugging and monitoring.\n")
2. **collections_spec** - parse error: Unexpected token: expected expression, found For
3. **capture_buffer_vreg_remapping_spec** - parse error: Unexpected token: expected identifier, found LParen
4. **collections_spec** - parse error: Unexpected token: expected expression, found For
5. **hello_spec** - failed to read test/basic/hello_spec.spl: No such file or directory (os error 2)

### Priority 3: Stabilize Flaky Tests (1)

Tests with intermittent failures:
- helpers_spec (20.0% failure rate)

