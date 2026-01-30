# Test Results

**Generated:** 2026-01-30 09:37:30
**Total Tests:** 152
**Status:** ⚠️ 5 FAILED

## Summary

| Status | Count | Percentage |
|--------|-------|-----------|
| ✅ Passed | 147 | 96.7% |
| ❌ Failed | 5 | 3.3% |
| ⏭️ Skipped | 0 | 0.0% |
| 🔕 Ignored | 0 | 0.0% |
| 🔐 Qualified Ignore | 0 | 0.0% |

---

## ❌ Failed Tests (5)

### 🔴 minimal_spec

**File:** `test/system/features/database_synchronization/minimal_spec.spl`
**Category:** System
**Failed:** 2026-01-30T09:33:02.394842346+00:00
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
**Failed:** 2026-01-30T09:33:02.394882905+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: function `args` not found
Location: test/system/features/fault_detection/fault_detection_spec.spl
```

---

### 🔴 parser_default_keyword_spec

**File:** `test/system/features/parser/parser_default_keyword_spec.spl`
**Category:** System
**Failed:** 2026-01-30T09:33:02.394970133+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected Colon, found Assign
Location: test/system/features/parser/parser_default_keyword_spec.spl
```

---

### 🔴 parser_skip_keyword_spec

**File:** `test/system/features/parser/parser_skip_keyword_spec.spl`
**Category:** System
**Failed:** 2026-01-30T09:37:30.199094394+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected expression, found Colon
Location: test/system/features/parser/parser_skip_keyword_spec.spl
```

---

### 🔴 parser_static_keyword_spec

**File:** `test/system/features/parser/parser_static_keyword_spec.spl`
**Category:** System
**Failed:** 2026-01-30T09:33:02.395019699+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected identifier, found Static
Location: test/system/features/parser/parser_static_keyword_spec.spl
```

---

---

## 📊 Timing Analysis

---

## 🎯 Action Items

### Priority 1: Fix Failing Tests (5)

1. **minimal_spec** - compile failed: parse: in "/home/ormastes/dev/pub/simple/src/lib/std/src/db/atomic.spl": Unexpected token: expected expression, found Indent
2. **fault_detection_spec** - compile failed: semantic: function `args` not found
3. **parser_default_keyword_spec** - parse error: Unexpected token: expected Colon, found Assign
4. **parser_skip_keyword_spec** - parse error: Unexpected token: expected expression, found Colon
5. **parser_static_keyword_spec** - parse error: Unexpected token: expected identifier, found Static

### Priority 3: Stabilize Flaky Tests (1)

Tests with intermittent failures:
- string_helpers_spec (83.3% failure rate)

