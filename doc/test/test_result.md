# Test Results

**Generated:** 2026-02-03 06:51:53
**Total Tests:** 44
**Status:** ⚠️ 44 FAILED

## Summary

| Status | Count | Percentage |
|--------|-------|-----------|
| ✅ Passed | 0 | 0.0% |
| ❌ Failed | 44 | 100.0% |
| ⏭️ Skipped | 0 | 0.0% |
| 🔕 Ignored | 0 | 0.0% |
| 🔐 Qualified Ignore | 0 | 0.0% |

---

## 🔄 Recent Status Changes

| Test | Change | Run |
|------|--------|-----|
| creates default configuration | new_test |  |
| allows custom configuration | new_test |  |
| supports disabling JIT | new_test |  |
| identifies Success as success | new_test |  |
| handles Success without address | new_test |  |
| identifies CompilationError as error | new_test |  |
| identifies CircularDependency as error | new_test |  |
| identifies UpdateFailed as error | new_test |  |
| identifies NotFound as neither success nor error | new_test |  |
| creates with default config | new_test |  |
| creates with custom config | new_test |  |
| initializes empty caches | new_test |  |
| loads metadata successfully | new_test |  |
| caches loaded metadata | new_test |  |
| handles missing SMF files | new_test |  |
| tracks loaded SMF count | new_test |  |
| returns false when JIT is disabled | new_test |  |
| returns false for unknown symbols | new_test |  |
| returns true for symbols in metadata | new_test |  |
| returns None for unknown symbols | new_test |  |

---

## ❌ Failed Tests (44)

### 🔴 handles update errors

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714520252+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'handles update errors' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 identifies UpdateFailed as error

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714434258+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'identifies UpdateFailed as error' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 adds to instantiations list

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714515633+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'adds to instantiations list' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 resolves registered symbols

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714551371+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'resolves registered symbols' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 creates with custom config

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714445149+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'creates with custom config' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 identifies NotFound as neither success nor error

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714438957+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'identifies NotFound as neither success nor error' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 returns None for unknown symbols

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714554427+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'returns None for unknown symbols' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 loads SMF metadata

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714563454+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'loads SMF metadata' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 handles Success without address

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714421945+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'handles Success without address' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 reports initial empty stats

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714526434+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'reports initial empty stats' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 propagates load errors

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714565959+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'propagates load errors' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 detects direct cycle

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714494863+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'detects direct cycle' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 caches JIT result

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714560208+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'caches JIT result' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 tracks cached compilations

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714529119+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'tracks cached compilations' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 returns CompilationError at max depth

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714488762+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'returns CompilationError at max depth' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 tracks loaded SMF files

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714532084+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'tracks loaded SMF files' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 identifies CircularDependency as error

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714428637+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'identifies CircularDependency as error' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 returns NotFound when disabled

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714485476+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'returns NotFound when disabled' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 creates with default config

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714442383+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'creates with default config' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 allows custom configuration

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714410152+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'allows custom configuration' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 returns NotFound for unknown symbol

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714497949+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'returns NotFound for unknown symbol' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 creates default configuration

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714404141+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'creates default configuration' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 handles missing SMF files

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714460348+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'handles missing SMF files' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 finds possible entry in loaded metadata

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714481668+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'finds possible entry in loaded metadata' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 loads metadata successfully

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714451280+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'loads metadata successfully' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 returns cached code

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714491617+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'returns cached code' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 tries JIT on miss

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714557342+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'tries JIT on miss' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 identifies Success as success

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714418408+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'identifies Success as success' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 initializes empty caches

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714448164+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'initializes empty caches' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 removes from possible list

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714504201+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'removes from possible list' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 skips SMF updates

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714523428+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'skips SMF updates' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 overwrites existing registration

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714547834+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'overwrites existing registration' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 updates metadata in memory

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714501226+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'updates metadata in memory' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 returns false for unknown symbols

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714470126+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'returns false for unknown symbols' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 identifies CompilationError as error

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714425501+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'identifies CompilationError as error' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 creates with default config

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714535110+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'creates with default config' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 caches loaded metadata

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714453966+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'caches loaded metadata' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 tracks loaded SMF count

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714464105+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'tracks loaded SMF count' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 supports disabling JIT

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714413438+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'supports disabling JIT' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 returns false when JIT is disabled

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714467111+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'returns false when JIT is disabled' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 returns true for symbols in metadata

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714475016+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'returns true for symbols in metadata' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 returns None for unknown symbols

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714478663+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'returns None for unknown symbols' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 creates with custom config

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714538286+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'creates with custom config' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

### 🔴 registers symbol address

**File:** `test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl`
**Category:** Unit
**Failed:** 2026-02-03T06:51:53.714541983+00:00
**Flaky:** No (100.0% failure rate)

**Error:**
```
Test 'registers symbol address' failed
Location: test/lib/std/unit/compiler/loader/jit_instantiator_spec.spl
```

---

---

## 📊 Timing Analysis

---

## 🎯 Action Items

### Priority 1: Fix Failing Tests (44)

1. **handles update errors** - Test 'handles update errors' failed
2. **identifies UpdateFailed as error** - Test 'identifies UpdateFailed as error' failed
3. **adds to instantiations list** - Test 'adds to instantiations list' failed
4. **resolves registered symbols** - Test 'resolves registered symbols' failed
5. **creates with custom config** - Test 'creates with custom config' failed

