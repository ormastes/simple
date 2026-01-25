# Test Results

**Generated:** 2026-01-25 03:28:28
**Total Tests:** 63
**Status:** ⚠️ 2 FAILED

## Summary

| Status | Count | Percentage |
|--------|-------|-----------|
| ✅ Passed | 61 | 96.8% |
| ❌ Failed | 2 | 3.2% |
| ⏭️ Skipped | 0 | 0.0% |
| 🔕 Ignored | 0 | 0.0% |
| 🔐 Qualified Ignore | 0 | 0.0% |

---

## ❌ Failed Tests (2)

### 🔴 progress_spec

**File:** `test/unit/spec/progress_spec.spl`
**Category:** Unit
**Failed:** 2026-01-25T03:28:28.586945283+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected fn, struct, class, enum, union, impl, mod, extern, or pub after attributes, found String("\nUnit tests for test progress reporting functionality.\n\nThis test file verifies the progress reporting API used during long-running tests:\n- Basic progress message output with timestamps\n- Percentage and step-based completion reporting\n- Progress formatting and string interpolation\n- Integration with slow tests and error scenarios\n\nThe progress function provides visibility into test execution for debugging and monitoring.\n")
Location: test/unit/spec/progress_spec.spl
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

### Priority 1: Fix Failing Tests (2)

1. **progress_spec** - parse error: Unexpected token: expected fn, struct, class, enum, union, impl, mod, extern, or pub after attributes, found String("\nUnit tests for test progress reporting functionality.\n\nThis test file verifies the progress reporting API used during long-running tests:\n- Basic progress message output with timestamps\n- Percentage and step-based completion reporting\n- Progress formatting and string interpolation\n- Integration with slow tests and error scenarios\n\nThe progress function provides visibility into test execution for debugging and monitoring.\n")
2. **hello_spec** - failed to read test/basic/hello_spec.spl: No such file or directory (os error 2)

### Priority 3: Stabilize Flaky Tests (1)

Tests with intermittent failures:
- helpers_spec (20.0% failure rate)

