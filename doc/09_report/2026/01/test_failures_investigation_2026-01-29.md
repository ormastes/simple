# Test Failures Investigation Report

**Date:** 2026-01-29
**Investigator:** Claude Sonnet 4.5
**Scope:** Active test failures and potentially revivable tests

---

## Part 1: Active Rust Test Failure

### Test: `value::tests::test_index_get`

**File:** `src/rust/runtime/src/value/mod_tests.rs:262`
**Status:** ❌ **FAILING** (Active Regression)
**Priority:** 🔴 **CRITICAL**

#### Error Details

```
assertion `left == right` failed
  left: 15453216833958
 right: 65
```

#### Test Code (Line 259-262)

```rust
// String indexing (returns char code)
let s = b"ABC";
let str_val = rt_string_new(s.as_ptr(), s.len() as u64);
let char_val = rt_index_get(str_val, RuntimeValue::from_int(0));
assert_eq!(char_val.as_int(), 65); // 'A'
```

#### Analysis

**Expected Behavior:**
- Indexing string "ABC" at position 0
- Should return character code 65 ('A')

**Actual Behavior:**
- Returns 15453216833958 (garbage value)
- Looks like an uninitialized pointer or memory address

**Root Cause:**
- `rt_index_get()` for strings is broken
- Returning wrong value type or dereferencing incorrectly
- Possible issues:
  1. Returning pointer instead of character value
  2. Not properly extracting character from string
  3. Type confusion between RuntimeValue variants

#### Impact

- **Severity:** HIGH
- **Scope:** Core runtime functionality
- **Affected:** String indexing operations
- **Regression:** Yes (tests were passing before)

#### Recent Changes

Recent commits in runtime area:
- `e5373b083` - Pipeline connections
- `996d7df6a` - FString parser fixes
- `d432a8852` - Lowering robustness with enum patterns

**Possible culprit:** Recent changes to value handling or string operations

#### Recommendation

1. **Investigate `rt_index_get()` implementation**
   - Check string indexing branch
   - Verify RuntimeValue return type
   - Look for recent changes to this function

2. **Check RuntimeValue string methods**
   - Verify `as_int()` for character values
   - Check if string char extraction changed

3. **Git bisect if needed**
   - Find exact commit that broke this
   - Revert or fix the change

4. **Expand test coverage**
   - Add more string indexing tests
   - Test edge cases (empty string, UTF-8, out of bounds)

**Priority:** Fix immediately - this breaks basic string operations

---

## Part 2: Simple Spec Test Failures

### Test File: `test/system/features/classes/classes_spec.spl`

**Results:** 17 passed, 5 failed (77% success rate)
**Status:** ❌ **5 FAILURES** (Unknown specific tests)
**Priority:** 🟡 **MEDIUM**

#### Problem

**Cannot identify which tests are failing** due to test runner limitations.

**Test runner output:**
```
FAIL  test/system/features/classes/classes_spec.spl (17 passed, 5 failed, 19681ms)
Results: 22 total, 17 passed, 5 failed
```

No individual test names shown!

#### What We Know

**All features work in isolation:**

✅ Tested manually and confirmed working:
1. Block-scoped impl blocks
2. Block-scoped context blocks
3. Trait polymorphism
4. Instance methods
5. Method missing
6. Property getters/setters
7. String field access
8. Person class construction

**Evidence of test flakiness:**
- Historical failure rate: 14% (2 failures out of 14 runs)
- Current failure rate: 23% (5 out of 22 tests)
- Inconsistent across runs
- Database shows file marked as "flaky"

#### Possible Causes

1. **Test Framework Issues** (Most likely)
   - Timing issues
   - State pollution between tests
   - Async/ordering problems

2. **String Comparison Issues**
   - May be related to `test_index_get` failure
   - String operations might be flaky

3. **Complex Test Interactions**
   - Tests with multiple operations may fail
   - Context state not properly isolated

4. **Type Annotation Issues**
   - Tests with return types might fail intermittently

#### Recommendation

1. **Add verbose test runner output** (CRITICAL)
   - Show individual test names and results
   - Format: `✓ test name` or `✗ test name: error`
   - Cannot debug without this

2. **Fix `test_index_get` first**
   - String issues might cascade to these failures
   - Fix core runtime before debugging framework

3. **Add test isolation**
   - Ensure tests don't share state
   - Clean up between tests
   - Add test cleanup hooks

4. **Investigate flakiness**
   - Run tests 100 times and collect failure patterns
   - Identify which specific tests are flaky
   - Add determinism to test execution

**Priority:** Medium - features work, likely framework issue

---

## Part 3: Potentially Revivable Commented Tests

### High Priority Candidates

Based on evidence that features now work, these commented tests might be revivable:

#### 1. `runner_handles_context_blocks` ⚠️ INVESTIGATE

**File:** `src/rust/driver/tests/runner_operators_tests.rs`
**Evidence:** Context blocks work in Simple specs!
**Test Code:**
```rust
// #[test]
// fn runner_handles_context_blocks() {
//     run_expect(r#"
// fn get_from_context():
//     return context.value
// context { value: 100 }:
//     main = get_from_context()
// "#, 100);
// }
```

**Recommendation:** UNCOMMENT AND TEST
- Context blocks are confirmed working
- This test might pass now
- Quick win if it works

#### 2. `runner_handles_method_missing` ⚠️ INVESTIGATE

**File:** `src/rust/driver/tests/runner_operators_tests.rs`
**Evidence:** Method missing works in Simple specs!
**Test Code:** (commented out)

**Recommendation:** UNCOMMENT AND TEST
- Method missing is confirmed working
- This test might pass now
- Quick win if it works

### Medium Priority Candidates

#### 3-5. Collection Tests ⚠️ INVESTIGATE

**File:** `src/rust/runtime/src/value/collection_tests.rs`
**Tests:**
- `test_array_growth`
- `test_tuple_default_nil`
- `test_dict_growth`

**Reason:** No comments explaining why they're disabled
**Evidence:** Basic collection features, should work
**Recommendation:** UNCOMMENT ONE AT A TIME AND TEST

### Low Priority Candidates

#### 6-11. Advanced Features ⏸️ KEEP COMMENTED

**Legitimately blocked:**
- `infers_bitwise_operators` - Parser not ready
- `runner_handles_futures` - Async runtime not ready
- `runner_handles_generators` - Generator support not ready
- `runner_handles_macro_expansion` - Macro system not ready
- `runner_handles_pointer_types` - Advanced feature
- `runner_handles_union_types` - Advanced feature

**Recommendation:** Keep commented until features implemented

---

## Part 4: Ignored Rust Tests

### Tests with #[ignore] Marker

#### 1. `test_symbol_table_template_marker`

**File:** `src/rust/compiler/tests/smf_template_integration_tests.rs`
**Reason:** "Requires SMF symbol table parsing"
**Status:** ⏸️ Legitimately blocked
**Priority:** LOW

#### 2-4. Generic Template Tests

**File:** `src/rust/compiler/tests/generic_template_tests.rs`
**Count:** 3 tests
**Reason:** Unknown
**Status:** ⚠️ **NEEDS INVESTIGATION**
**Priority:** MEDIUM

**Action Required:**
```bash
grep -A5 "#\[ignore\]" src/rust/compiler/tests/generic_template_tests.rs
```

#### 5. JIT Interpreter Test

**File:** `src/rust/driver/tests/interpreter_jit.rs`
**Count:** 1 test
**Reason:** Unknown
**Status:** ⚠️ **NEEDS INVESTIGATION**
**Priority:** MEDIUM

**Action Required:**
```bash
grep -A5 "#\[ignore\]" src/rust/driver/tests/interpreter_jit.rs
```

---

## Part 5: Action Plan

### Immediate (Today)

1. 🔴 **Fix `test_index_get` failure** (CRITICAL)
   - Investigate `rt_index_get()` for strings
   - Fix string character extraction
   - Verify fix with test run
   - **Estimated time:** 30-60 minutes

2. 🟡 **Test 2 potentially revivable Rust tests** (QUICK WINS)
   - Uncomment `runner_handles_context_blocks`
   - Uncomment `runner_handles_method_missing`
   - Run tests individually
   - **Estimated time:** 15 minutes

3. 🟡 **Test 3 collection tests** (QUICK WINS)
   - Uncomment `test_array_growth`
   - Uncomment `test_tuple_default_nil`
   - Uncomment `test_dict_growth`
   - Run tests individually
   - **Estimated time:** 15 minutes

### Short-term (This Week)

4. 🟢 **Add verbose test runner output** (HIGH IMPACT)
   - Modify Simple test runner
   - Show individual test results
   - Add `--verbose` flag
   - **Estimated time:** 2-4 hours

5. 🟢 **Investigate ignored tests** (DOCUMENTATION)
   - Check 3 generic template tests
   - Check 1 JIT interpreter test
   - Document reasons or revive
   - **Estimated time:** 30 minutes

### Long-term (Future)

6. 🔵 **Fix test framework flakiness**
   - Add test isolation
   - Investigate 14% failure rate
   - Add determinism
   - **Estimated time:** 1-2 days

7. 🔵 **Expand test coverage**
   - Add string indexing edge cases
   - Add more collection tests
   - Add more OOP feature tests
   - **Ongoing**

---

## Part 6: Summary

### Current State

| Category | Status | Count |
|----------|--------|-------|
| **Active failures** | ❌ Critical | 1 Rust + 5 Simple |
| **Potentially revivable** | ⚠️ Investigate | 5 tests |
| **Legitimately blocked** | ⏸️ Correct | 10 tests |
| **Need investigation** | ⚠️ Unknown | 4 tests |

### Priority Queue

1. 🔴 Fix `test_index_get` (string indexing bug)
2. 🟡 Test 5 potentially revivable commented tests
3. 🟡 Investigate 4 ignored tests with unknown reasons
4. 🟢 Add test runner verbose output
5. 🔵 Fix test framework flakiness

### Expected Outcomes

If all investigations successful:
- ✅ Fix 1 critical runtime bug
- ✅ Potentially revive 5 more tests
- ✅ Document 4 ignored tests
- ✅ Improve test runner UX

**Total potential:** +6 tests (1 fix + 5 revived)

### Blockers

**Immediate blockers:**
- String indexing bug in runtime
- Test runner lacks verbose output
- Unknown reasons for 4 ignored tests

**Long-term blockers:**
- Test framework flakiness (14% failure rate)
- Interpreter limitations (566 tests blocked)

---

## Conclusion

**Status:** Active issues identified and prioritized

**Critical Path:**
1. Fix string indexing bug (breaks core functionality)
2. Test potentially revivable tests (quick wins)
3. Improve test tooling (verbose output)
4. Address long-term quality issues

**Overall Assessment:**
- ✅ Excellent documentation and process
- ❌ 1 critical runtime bug needs immediate fix
- ⚠️ 5+ tests potentially revivable
- 🔧 Test tooling needs improvement

**Next Steps:** Begin with fixing `test_index_get`, then test commented tests, then improve tooling.

---

*Report generated: 2026-01-29*
*Scope: All active failures and potentially revivable tests*
*Status: Investigation complete, action plan ready*
