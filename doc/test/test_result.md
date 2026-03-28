# Test Results

**Generated:** 2026-03-28 12:27:23
**Total Tests:** 5561
**Status:** ⚠️ 4 FAILED

## Summary

| Status | Count | Percentage |
|--------|-------|-----------|
| ✅ Passed | 5446 | 97.9% |
| ❌ Failed | 4 | 0.1% |
| ⏭️ Skipped | 111 | 2.0% |
| 🔕 Ignored | 0 | 0.0% |
| 🔐 Qualified Ignore | 0 | 0.0% |

---

## 🔄 Recent Status Changes

| Test | Change | Run |
|------|--------|-----|
| normalizes date suffixed slugs | new_test |  |
| extracts relative paths from markdown and plain text | new_test |  |
| extracts REQ and NFR identifiers | new_test |  |
| maps compiler sources to unit candidates | new_test |  |
| maps lib sources to unit candidates | new_test |  |
| maps source directories to integration candidates | new_test |  |
| warns when a requirement identifier is not covered | new_test |  |
| warns on legacy requirement roots in specs | new_test |  |
| warns when docs point to raw specs | new_test |  |
| warns for opted-in source roots without unit tests | new_test |  |
| normalizes date suffixed slugs | fail_to_pass |  |
| maps compiler sources to unit candidates | fail_to_pass |  |
| maps lib sources to unit candidates | fail_to_pass |  |
| maps source directories to integration candidates | fail_to_pass |  |
| extracts REQ and NFR identifiers | fail_to_pass |  |
| extracts relative paths from markdown and plain text | fail_to_pass |  |
| backend_port_feature_spec | new_test |  |
| bootstrap_spec | new_test |  |
| code_quality_tools_spec | new_test |  |
| codegen_parity_completion_spec | new_test |  |

---

## ❌ Failed Tests (4)

### 🔴 warns on legacy requirement roots in specs

**File:** `test/unit/app/tooling/traceability_spec.spl`
**Category:** Unit
**Failed:** 
**Flaky:** No (100.0% failure rate)

---

### 🔴 warns for opted-in source roots without unit tests

**File:** `test/unit/app/tooling/traceability_spec.spl`
**Category:** Unit
**Failed:** 
**Flaky:** No (100.0% failure rate)

---

### 🔴 warns when docs point to raw specs

**File:** `test/unit/app/tooling/traceability_spec.spl`
**Category:** Unit
**Failed:** 
**Flaky:** No (100.0% failure rate)

---

### 🔴 warns when a requirement identifier is not covered

**File:** `test/unit/app/tooling/traceability_spec.spl`
**Category:** Unit
**Failed:** 
**Flaky:** No (100.0% failure rate)

---

---

## 📊 Timing Analysis

---

## 🎯 Action Items

### Priority 1: Fix Failing Tests (4)

1. **warns on legacy requirement roots in specs** - 
2. **warns for opted-in source roots without unit tests** - 
3. **warns when docs point to raw specs** - 
4. **warns when a requirement identifier is not covered** - 

### Priority 3: Stabilize Flaky Tests (6)

Tests with intermittent failures:
- maps lib sources to unit candidates (24.0% failure rate)
- extracts relative paths from markdown and plain text (36.0% failure rate)
- extracts REQ and NFR identifiers (32.0% failure rate)
- maps source directories to integration candidates (24.0% failure rate)
- normalizes date suffixed slugs (4.0% failure rate)

