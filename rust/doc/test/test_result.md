# Test Results

**Generated:** 2026-02-02 00:47:02
**Total Tests:** 14
**Status:** ⚠️ 7 FAILED

## Summary

| Status | Count | Percentage |
|--------|-------|-----------|
| ✅ Passed | 7 | 50.0% |
| ❌ Failed | 7 | 50.0% |
| ⏭️ Skipped | 0 | 0.0% |
| 🔕 Ignored | 0 | 0.0% |
| 🔐 Qualified Ignore | 0 | 0.0% |

---

## 🔄 Recent Status Changes

| Test | Change | Run |
|------|--------|-----|
| sdn_minimal_spec | new_test |  |

---

## ❌ Failed Tests (7)

### 🔴 tensor_bridge_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/math/tensor_bridge_spec.spl`
**Category:** System
**Failed:** 2026-02-01T04:24:13.075696350+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected pattern, found Flat
Location: /home/ormastes/dev/pub/simple/test/system/features/math/tensor_bridge_spec.spl
```

---

### 🔴 mat4_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/math/mat4_spec.spl`
**Category:** System
**Failed:** 2026-02-01T04:24:13.075531565+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
compile failed: semantic: variable `group_stack` not found
Location: /home/ormastes/dev/pub/simple/test/system/features/math/mat4_spec.spl
```

---

### 🔴 fixed_size_arrays_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/arrays/fixed_size_arrays_spec.spl`
**Category:** System
**Failed:** 2026-02-01T02:35:55.934721841+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected indented block after ':', found Context
Location: /home/ormastes/dev/pub/simple/test/system/features/arrays/fixed_size_arrays_spec.spl
```

---

### 🔴 sdn_minimal_spec

**File:** `test/tmp/sdn_minimal_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-02T00:47:02.940078024+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
failed to read test/tmp/sdn_minimal_spec.spl: No such file or directory (os error 2)
Location: test/tmp/sdn_minimal_spec.spl
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

### 🔴 type_conversion_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/arrays/type_conversion_spec.spl`
**Category:** System
**Failed:** 2026-02-01T02:35:55.935152775+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
parse error: Unexpected token: expected indented block after ':', found Identifier { name: "it", pattern: Immutable }
Location: /home/ormastes/dev/pub/simple/test/system/features/arrays/type_conversion_spec.spl
```

---

### 🔴 fixed_size_edge_cases_spec

**File:** `home/ormastes/dev/pub/simple/test/system/features/arrays/fixed_size_edge_cases_spec.spl`
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

### Priority 1: Fix Failing Tests (7)

1. **tensor_bridge_spec** - parse error: Unexpected token: expected pattern, found Flat
2. **mat4_spec** - compile failed: semantic: variable `group_stack` not found
3. **fixed_size_arrays_spec** - parse error: Unexpected token: expected indented block after ':', found Context
4. **sdn_minimal_spec** - failed to read test/tmp/sdn_minimal_spec.spl: No such file or directory (os error 2)
5. **comment_only_spec** - compile failed: semantic: variable `group_stack` not found

