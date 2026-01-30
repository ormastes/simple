# Test Results

**Generated:** 2026-01-30 09:45:50
**Total Tests:** 180
**Status:** ⚠️ 2 FAILED

## Summary

| Status | Count | Percentage |
|--------|-------|-----------|
| ✅ Passed | 178 | 98.9% |
| ❌ Failed | 2 | 1.1% |
| ⏭️ Skipped | 0 | 0.0% |
| 🔕 Ignored | 0 | 0.0% |
| 🔐 Qualified Ignore | 0 | 0.0% |

---

## ❌ Failed Tests (2)

### 🔴 minimal_spec

**File:** `test/system/features/database_synchronization/minimal_spec.spl`
**Category:** System
**Failed:** 2026-01-30T09:44:36.810182616+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/db/atomic.spl": Unexpected token: expected expression, found Indent
Location: test/system/features/database_synchronization/minimal_spec.spl
```

---

### 🔴 fault_detection_spec

**File:** `test/system/features/fault_detection/fault_detection_spec.spl`
**Category:** System
**Failed:** 2026-01-30T09:43:29.664968334+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `args` not found
Location: test/system/features/fault_detection/fault_detection_spec.spl
```

---

---

## 📊 Timing Analysis

---

## 🎯 Action Items

### Priority 1: Fix Failing Tests (2)

1. **minimal_spec** - compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/db/atomic.spl": Unexpected token: expected expression, found Indent
2. **fault_detection_spec** - compile failed: semantic: function `args` not found

### Priority 3: Stabilize Flaky Tests (3)

Tests with intermittent failures:
- parser_skip_keyword_spec (55.6% failure rate)
- string_helpers_spec (83.3% failure rate)
- parser_default_keyword_spec (20.0% failure rate)

