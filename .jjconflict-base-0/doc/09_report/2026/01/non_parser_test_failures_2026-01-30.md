# Non-Parser Test Failures Analysis

**Generated:** 2026-01-30
**Total Test Failures:** 92
**Parser Failures (Excluded):** 75 (81.5%)
**Non-Parser Failures:** 17 (18.5%)

## Executive Summary

Out of 92 failing tests, **75 are parser errors** which are excluded from this analysis. The remaining **17 failures** fall into 4 categories:

| Category | Count | Percentage | Priority |
|----------|-------|------------|----------|
| Missing File | 9 | 52.9% | 🔴 HIGH |
| Encoding (UTF-8) | 3 | 17.6% | 🟡 MEDIUM |
| Timeout | 3 | 17.6% | 🟡 MEDIUM |
| Semantic | 2 | 11.8% | 🔴 HIGH |

---

## 🔴 Category 1: Missing File Errors (9 failures)

**Root Cause:** Test files do not exist at specified paths

### Failures

1. **actor_model_spec**
   - File: `tmp/actor_model_spec.spl`
   - Error: No such file or directory

2. **hello_spec**
   - File: `test/basic/hello_spec.spl`
   - Error: No such file or directory

3. **metrics_spec**
   - File: `test/lib/std/unit/metrics_spec.spl`
   - Error: No such file or directory

4. **sys_ffi_spec**
   - File: `test/lib/std/unit/sys_ffi_spec.spl`
   - Error: No such file or directory

5. **force_fields_spec**
   - File: `test/lib/std/unit/physics/dynamics/force_fields_spec.spl`
   - Error: No such file or directory

6. **context_pack_spec**
   - File: `test/lib/std/unit/context_pack_spec.spl`
   - Error: No such file or directory

7. **server_spec**
   - File: `test/lib/std/unit/server_spec.spl`
   - Error: No such file or directory

8. **test_actor_model_spec**
   - File: `test/lib/std/unit/game_engine/test_actor_model_spec.spl`
   - Error: No such file or directory

9. **set_spec**
   - File: `test/lib/std/unit/core/set_spec.spl`
   - Error: No such file or directory

### Recommended Actions

**Immediate:**
- [ ] Verify if these tests were moved/renamed/deleted
- [ ] Check git history: `jj log -r :: -- <file_path>`
- [ ] Remove stale test entries from test database

**Investigation:**
- [ ] `/tmp` tests may be temporary test files that weren't cleaned up
- [ ] `test/lib/std/unit/` tests may have been reorganized

**Fix Options:**
1. **Option A:** Remove test references from database if tests were intentionally deleted
2. **Option B:** Restore test files if they were accidentally removed
3. **Option C:** Update test paths if files were moved

---

## 🟡 Category 2: Encoding Errors (3 failures)

**Root Cause:** Files contain invalid UTF-8 sequences

### Failures

1. **arg_parsing_spec**
   - File: `test/lib/std/unit/tooling/arg_parsing_spec.spl`
   - Error: stream did not contain valid UTF-8

2. **contact2_spec**
   - File: `test/lib/std/unit/physics/collision/contact2_spec.spl`
   - Error: stream did not contain valid UTF-8

3. **min_test_spec**
   - File: `tmp/min_test_spec.spl`
   - Error: stream did not contain valid UTF-8

### Recommended Actions

**Diagnostic Commands:**
```bash
# Check file encoding
file test/lib/std/unit/tooling/arg_parsing_spec.spl
file test/lib/std/unit/physics/collision/contact2_spec.spl

# Find invalid UTF-8 sequences
iconv -f utf-8 -t utf-8 test/lib/std/unit/tooling/arg_parsing_spec.spl

# Check for binary content
hexdump -C test/lib/std/unit/tooling/arg_parsing_spec.spl | head
```

**Fix Options:**
1. **If corrupted:** Restore from git history
2. **If intentionally binary:** Move out of test directory
3. **If encoding issue:** Convert to UTF-8:
   ```bash
   iconv -f ISO-8859-1 -t UTF-8 input.spl > output.spl
   ```

---

## 🟡 Category 3: Timeout Errors (3 failures)

**Root Cause:** Tests exceed 30-second timeout limit

### Failures

1. **cli_spec**
   - File: `test/lib/std/unit/cli_spec.spl`
   - Timeout: 30 seconds

2. **spec_framework_spec**
   - File: `test/lib/std/system/spec/spec_framework_spec.spl`
   - Timeout: 30 seconds

3. **fixture_spec**
   - File: `test/lib/std/fixtures/fixture_spec.spl`
   - Timeout: 30 seconds

### Recommended Actions

**Immediate:**
- [ ] Run tests individually to see which specific test cases timeout
- [ ] Check for infinite loops or deadlocks

**Diagnostic Commands:**
```bash
# Run with verbose output
./target/release/simple_old test test/lib/std/unit/cli_spec.spl -v

# Run with increased timeout
./target/release/simple_old test test/lib/std/unit/cli_spec.spl --timeout=120

# Profile performance
./target/release/simple_old test test/lib/std/unit/cli_spec.spl --profile
```

**Possible Causes:**
1. **Infinite loops** in test code
2. **Slow I/O operations** without mocking
3. **Network requests** that hang
4. **Large test data** processing
5. **Deadlocks** in concurrent code

**Fix Options:**
1. **Option A:** Increase timeout for slow tests (mark as `slow_it`)
2. **Option B:** Optimize test performance
3. **Option C:** Break into smaller test cases
4. **Option D:** Mock slow operations (file I/O, network)

---

## 🔴 Category 4: Semantic Errors (2 failures)

**Root Cause:** Compiler semantic analysis failures

### Failures

1. **constructor_spec**
   - File: `test/lib/std/unit/constructor_spec.spl`
   - Error: Native compilation failed
   - Type: Compilation error

2. **feature_doc_spec**
   - File: `test/lib/std/system/spec/feature_doc_spec.spl`
   - Error: `cannot modify self.features in immutable fn method`
   - Type: Mutability error

### Detailed Analysis

#### 1. constructor_spec - Native Compilation Failure

**Error:**
```
Native compilation failed: Failed to compile test/lib/std/unit/constructor_spec.spl to native binary
```

**Potential Causes:**
- Codegen bug for specific language constructs
- LLVM/Cranelift backend issue
- Missing FFI bindings

**Recommended Actions:**
```bash
# Read the test file
cat test/lib/std/unit/constructor_spec.spl

# Try interpreter mode (non-native)
./target/release/simple_old test test/lib/std/unit/constructor_spec.spl --no-native

# Get detailed error
./target/release/simple_old test test/lib/std/unit/constructor_spec.spl -vv 2>&1 | grep -A 20 "compilation failed"
```

#### 2. feature_doc_spec - Mutability Error

**Error:**
```
cannot modify self.features in immutable fn method
```

**Root Cause:** Trying to mutate `self` in an immutable method (using `fn` instead of `me`)

**Fix:**
```simple
# ❌ WRONG - immutable method trying to mutate
impl FeatureDoc:
    fn add_feature(feature: Feature):
        self.features.push(feature)  # Error: can't modify

# ✅ CORRECT - use mutable method
impl FeatureDoc:
    me add_feature(feature: Feature):
        self.features.push(feature)  # OK: 'me' allows mutation
```

**Recommended Actions:**
- [ ] Read test file and identify the problematic method
- [ ] Change `fn` to `me` for methods that modify `self`
- [ ] Or refactor to use immutable operations (return new instance)

---

## Summary Statistics

### Failure Distribution

```
Non-Parser Failures: 17 total
├── Missing File: 9 (53%) - HIGH PRIORITY
├── Encoding:     3 (18%) - MEDIUM PRIORITY
├── Timeout:      3 (18%) - MEDIUM PRIORITY
└── Semantic:     2 (12%) - HIGH PRIORITY
```

### Priority Breakdown

| Priority | Count | Action Required |
|----------|-------|-----------------|
| 🔴 HIGH | 11 | Immediate fix needed |
| 🟡 MEDIUM | 6 | Investigate and optimize |

---

## Recommended Fix Order

### Phase 1: Quick Wins (Missing Files)
1. Remove 9 stale test entries from database
2. Or restore missing files from git history
3. **Estimated Time:** 15-30 minutes
4. **Impact:** Removes 53% of non-parser failures

### Phase 2: Semantic Errors
1. Fix `feature_doc_spec` mutability issue (change `fn` to `me`)
2. Investigate `constructor_spec` native compilation failure
3. **Estimated Time:** 30-60 minutes
4. **Impact:** Removes 12% of failures, unblocks feature documentation

### Phase 3: Encoding Issues
1. Diagnose UTF-8 encoding problems in 3 files
2. Fix or remove corrupted files
3. **Estimated Time:** 30 minutes
4. **Impact:** Removes 18% of failures

### Phase 4: Timeout Investigation
1. Profile slow tests
2. Either optimize or mark as `slow_it`
3. **Estimated Time:** 1-2 hours
4. **Impact:** Removes 18% of failures

---

## Expected Outcomes

### After Quick Wins (Phase 1)
- ✅ Failures reduced from 92 to 83 (10% improvement)
- ✅ Non-parser failures reduced from 17 to 8
- ✅ Test database cleaned up

### After All Fixes
- ✅ Non-parser failures: 0
- ✅ Remaining failures: 75 parser errors only
- ✅ Overall pass rate: 89.6% → 91.8%

### After Parser Fixes (Future)
- ✅ All 912 tests passing (100%)
- ✅ Full test suite green

---

## Parser Failures (Excluded from Analysis)

**Total:** 75 failures (81.5% of all failures)

**Common Parser Errors:**
- `Unexpected token: expected expression, found <token>`
- `Unexpected token: expected identifier, found <token>`
- `Unexpected token: expected Fn, found Static`

**Sample Failed Tests:**
- test_inject_spec
- trait_coherence_spec
- parser_196_spec
- assets_spec
- activation_spec
- ui_structural_patchset_spec
- fuzz_spec
- arg_parsing_spec
- promise_spec
- server_spec
- ... and 65 more

**Note:** Parser failures are tracked separately and will be addressed in a dedicated parser fix session.

---

## Files for Investigation

Create investigation checklist:

```bash
# Missing files (verify existence)
ls -la test/basic/hello_spec.spl
ls -la test/lib/std/unit/metrics_spec.spl
ls -la test/lib/std/unit/sys_ffi_spec.spl
ls -la test/lib/std/unit/physics/dynamics/force_fields_spec.spl
ls -la test/lib/std/unit/context_pack_spec.spl
ls -la test/lib/std/unit/server_spec.spl
ls -la test/lib/std/unit/game_engine/test_actor_model_spec.spl
ls -la test/lib/std/unit/core/set_spec.spl

# Encoding errors (check file type)
file test/lib/std/unit/tooling/arg_parsing_spec.spl
file test/lib/std/unit/physics/collision/contact2_spec.spl

# Semantic errors (read source)
cat test/lib/std/unit/constructor_spec.spl
cat test/lib/std/system/spec/feature_doc_spec.spl

# Timeout errors (profile)
time ./target/release/simple_old test test/lib/std/unit/cli_spec.spl
time ./target/release/simple_old test test/lib/std/system/spec/spec_framework_spec.spl
time ./target/release/simple_old test test/lib/std/fixtures/fixture_spec.spl
```

---

## Next Steps

1. **Run investigation commands** to verify missing files
2. **Clean test database** to remove stale entries
3. **Fix semantic errors** (mutability issues)
4. **Diagnose encoding problems** in 3 files
5. **Profile timeout tests** to identify bottlenecks
6. **Update this report** with findings

---

## Appendix: Full Error Details

Detailed error messages for all 17 non-parser failures are available in:
- `doc/test/test_result.md` (generated test report)
- `doc/test/test_db.sdn` (test execution database)

For parser error details, see separate parser error analysis (not included in this report).
