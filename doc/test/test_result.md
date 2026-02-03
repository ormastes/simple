# Test Results

**Generated:** 2026-02-03 03:35:17
**Total Tests:** 67
**Status:** ⚠️ 37 FAILED

## Summary

| Status | Count | Percentage |
|--------|-------|-----------|
| ✅ Passed | 30 | 44.8% |
| ❌ Failed | 37 | 55.2% |
| ⏭️ Skipped | 0 | 0.0% |
| 🔕 Ignored | 0 | 0.0% |
| 🔐 Qualified Ignore | 0 | 0.0% |

---

## 🔄 Recent Status Changes

| Test | Change | Run |
|------|--------|-----|
| creates lexer with source | new_test |  |
| initializes indent stack with zero | new_test |  |
| initializes with no pending dedents | new_test |  |
| starts with normal lexer mode | new_test |  |
| checks if at end with empty source | new_test |  |
| checks if at end with content | new_test |  |
| peeks at current character | new_test |  |
| peeks at next character | new_test |  |
| advances position | new_test |  |
| scans identifier | new_test |  |
| scans integer number | new_test |  |
| scans plus operator | new_test |  |
| scans minus operator | new_test |  |
| scans asterisk operator | new_test |  |
| scans slash operator | new_test |  |
| scans equals operator | new_test |  |
| recognizes val keyword | new_test |  |
| recognizes var keyword | new_test |  |
| recognizes fn keyword | new_test |  |
| recognizes if keyword | new_test |  |

---

## ❌ Failed Tests (37)

### 🔴 recognizes else keyword

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596312104+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'recognizes else keyword' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans simple string

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596364524+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans simple string' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans underscore identifier

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596475356+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans underscore identifier' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans or operator

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596423677+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans or operator' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans binary number

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596389191+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans binary number' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans greater than or equal

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596412556+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans greater than or equal' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 recognizes match keyword

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596320360+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'recognizes match keyword' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans equality

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596415361+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans equality' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 recognizes return keyword

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596326001+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'recognizes return keyword' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans hex number

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596386226+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans hex number' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans identifier with numbers

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596478772+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans identifier with numbers' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans empty string

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596367480+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans empty string' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 recognizes case keyword

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596323426+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'recognizes case keyword' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans less than

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596404571+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans less than' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans not operator

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596426082+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans not operator' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 skips spaces between tokens

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596468332+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'skips spaces between tokens' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans identifier

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596272509+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans identifier' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 recognizes if keyword

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596306043+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'recognizes if keyword' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans identifier with underscores

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596481718+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans identifier with underscores' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 recognizes while keyword

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596315050+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'recognizes while keyword' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans float with decimal

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596383220+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans float with decimal' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 recognizes fn keyword

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596303317+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'recognizes fn keyword' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans greater than

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596407236+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans greater than' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 recognizes val keyword

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596297687+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'recognizes val keyword' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans octal number

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596391846+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans octal number' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans and operator

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596420852+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans and operator' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans zero

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596374583+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans zero' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 skips tabs

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596471648+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'skips tabs' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans multi-digit integer

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596380565+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans multi-digit integer' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 skips single-line comment

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596398128+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'skips single-line comment' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans single digit

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596377569+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans single digit' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 recognizes for keyword

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596317725+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'recognizes for keyword' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 tracks line numbers

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596458744+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'tracks line numbers' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans integer number

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596275775+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans integer number' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans string with spaces

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596371047+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans string with spaces' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 scans less than or equal

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596409680+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'scans less than or equal' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

### 🔴 recognizes var keyword

**File:** `test/compiler/lexer_comprehensive_spec.spl`
**Category:** Unknown
**Failed:** 2026-02-03T03:35:17.596300793+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'recognizes var keyword' failed
Location: test/compiler/lexer_comprehensive_spec.spl
```

---

---

## 📊 Timing Analysis

---

## 🎯 Action Items

### Priority 1: Fix Failing Tests (37)

1. **recognizes else keyword** - Test 'recognizes else keyword' failed
2. **scans simple string** - Test 'scans simple string' failed
3. **scans underscore identifier** - Test 'scans underscore identifier' failed
4. **scans or operator** - Test 'scans or operator' failed
5. **scans binary number** - Test 'scans binary number' failed

