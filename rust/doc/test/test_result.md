# Test Results

**Generated:** 2026-02-01 02:35:55
**Total Tests:** 7
**Status:** ⚠️ 4 FAILED

## Summary

| Status | Count | Percentage |
|--------|-------|-----------|
| ✅ Passed | 3 | 42.9% |
| ❌ Failed | 4 | 57.1% |
| ⏭️ Skipped | 0 | 0.0% |
| 🔕 Ignored | 0 | 0.0% |
| 🔐 Qualified Ignore | 0 | 0.0% |

---

## ❌ Failed Tests (4)

### 🔴 type_conversion_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/arrays/type_conversion_spec.spl`
**Category:** System
**Failed:** 2026-02-01T02:35:55.935152775+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected indented block after ':', found Identifier { name: "it", pattern: Immutable }
Location: /home/ormastes/dev/pub/simple/test/system/features/arrays/type_conversion_spec.spl
```

---

### 🔴 fixed_size_arrays_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/arrays/fixed_size_arrays_spec.spl`
**Category:** System
**Failed:** 2026-02-01T02:35:55.934721841+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected indented block after ':', found Context
Location: /home/ormastes/dev/pub/simple/test/system/features/arrays/fixed_size_arrays_spec.spl
```

---

### 🔴 comment_only_spec

**File:** `home/ormastes/dev/pub/simple/rust/test/meta/comment_only_spec.spl`
**Category:** Unknown
**Failed:** 2026-01-31T09:32:37.751992043+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `group_stack` not found
Location: /home/ormastes/dev/pub/simple/rust/test/meta/comment_only_spec.spl
```

---

### 🔴 fixed_size_edge_cases_spec

**File:** `/home/ormastes/dev/pub/simple/test/system/features/arrays/fixed_size_edge_cases_spec.spl`
**Category:** System
**Failed:** 2026-02-01T02:35:55.934809639+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Slice
Location: /home/ormastes/dev/pub/simple/test/system/features/arrays/fixed_size_edge_cases_spec.spl
```

---

---

## 📊 Timing Analysis

---

## 🎯 Action Items

### Priority 1: Fix Failing Tests (4)

1. **type_conversion_spec** - parse error: Unexpected token: expected indented block after ':', found Identifier { name: "it", pattern: Immutable }
2. **fixed_size_arrays_spec** - parse error: Unexpected token: expected indented block after ':', found Context
3. **comment_only_spec** - compile failed: semantic: variable `group_stack` not found
4. **fixed_size_edge_cases_spec** - parse error: Unexpected token: expected pattern, found Slice

