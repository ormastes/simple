# Database Test Extended Workaround Analysis

**Date:** 2026-02-07
**Status:** Work in Progress
**Test Results:** 18/35 passing (51.4%), 17 failures remain

## Problem Summary

The bootstrap runtime (27MB pre-built binary) has a critical bug where using the `?` operator inside loops causes "try: early return" errors. This affects database extended tests which use `?` extensively for Option unwrapping.

## Error Categories

### 1. "try: early return" (8 test failures)

**Root Cause:** Using `?` operator to unwrap Options inside `for` loops triggers runtime error.

**Problem Pattern:**
```simple
for row in table.rows:
    val id = row.get_i64("id")?  # ❌ Fails with "try: early return"
    if id == target:
        return row.get_i64("value")?  # ❌ Also fails
```

**Solution Pattern:**
```simple
for row in table.rows:
    val id = row.get_i64("id") ?? -1  # ✅ Use ?? instead of ?
    if id != -1 and id == target:
        val value = row.get_i64("value") ?? -1  # ✅ Unwrap with default
        if value != -1:
            return value
```

### 2. "cannot convert enum to float" (9 test failures)

**Root Cause:** Passing `Option<f64>` (from `row.get_f64()`) directly to struct constructor fails type checking.

**Problem Pattern:**
```simple
return Some(TimingSummary(
    test_id: test_id,
    mean: row.get_f64("mean")?      # ❌ Option<f64> → f64 fails
))
```

**Solution Pattern:**
```simple
val mean = row.get_f64("mean") ?? 0.0  # ✅ Unwrap to f64 FIRST
return Some(TimingSummary(
    test_id: test_id,
    mean: mean  # ✅ Now it's plain f64
))
```

## Methods Fixed (Partial)

### Fixed Methods:
1. ✅ `get_file_id(path: text) -> i64?` - Query method
2. ✅ `get_suite_id(file_path, suite_name) -> i64?` - Query method
3. ✅ `get_test_id(file_path, suite_name, test_name) -> i64?` - Query method
4. ✅ `get_counter(test_id) -> CounterRecord?` - Stats query
5. ✅ `get_timing_summary(test_id) -> TimingSummary?` - Timing query
6. ✅ `get_or_create_file(path) -> i64` - Creation method
7. ✅ `get_or_create_suite(file_path, suite_name) -> i64` - Creation method
8. ✅ `get_or_create_test(suite_id, test_name) -> i64` - Creation method

### Remaining Methods with `?` in Loops:
1. ❌ `list_runs(status_filter) -> [RunRecord]` - Lines 997-1017 (6 `?` uses)
2. ❌ `all_test_info() -> [TestInfo]` - Lines 1024-1065 (9 `?` uses)
3. ❌ `get_suite_info(suite_id) -> (text, text)?` - Not yet checked
4. ❌ `collect_timing_runs(test_id, max_count) -> [f64]` - Already uses .? properly (lines 648-663)
5. ❌ Other helper methods

## Why Fixes Haven't Solved All Tests

**Hypothesis:** Even though I fixed the query methods (get_file_id, get_suite_id, etc.), the tests are still failing. This suggests:

1. **Caching Issue:** Runtime might be caching parsed code
2. **Indirect Calls:** Tests might call OTHER methods that internally use `?` in loops
3. **Multiple Locations:** The same method names might exist in multiple places
4. **Additional Methods:** More methods beyond the 8 I fixed need the same workaround

## Verification Needed

To confirm which methods are actually being called, we need to:

1. Add debug prints to the fixed methods to verify they're being executed
2. Check if there are duplicate method definitions
3. Trace the exact call path from failing tests to the error location
4. Verify the runtime is actually re-parsing the modified source

## Next Steps

### Option A: Systematic Fix (8-10 hours)
- Find ALL 54 locations with `?` in loops
- Apply workaround pattern to each
- Test incrementally
- Document each fix

### Option B: Targeted Fix (2-3 hours)
- Focus on the 3 failing test groups:
  - Test Hierarchy Creation (3 tests)
  - Counter Updates (6 tests)
  - Timing Statistics (5 tests)
  - Integration (3 tests)
- Trace exact call paths
- Fix only the methods these tests actually call

### Option C: Runtime Update (blocked)
- Rebuild bootstrap runtime with fix
- Not possible - Rust source deleted 2026-02-06
- Must wait for official runtime update

## Proven Workaround Pattern

This pattern has been proven to work in collections tests (60/60 passing):

```simple
# BEFORE (fails):
fn query_method() -> T?:
    val table = db.get_table("name")?  # Early return error
    for row in table.rows:
        val field = row.get_i64("field")?  # Early return error
        if condition:
            return field

# AFTER (works):
fn query_method() -> T?:
    val table_opt = db.get_table("name")
    if not table_opt.?:
        return None
    val table = table_opt?  # Unwrap OUTSIDE loop

    for row in table.rows:
        val field = row.get_i64("field") ?? -1  # Use ?? not ?
        if field != -1 and condition:
            return Some(field)

    None
```

## Files Modified

- **`src/lib/database/test_extended.spl`** - Lines 808-1070
  - 8 methods partially fixed
  - ~46 more locations need fixing

## Related Documentation

- `doc/report/collections_runtime_bugs_fixed_2026-02-07.md` - Proven pattern
- `doc/report/runtime_parser_bugs_2026-02-06.md` - Runtime bug catalog
- `MEMORY.md` - Critical limitations reference

## Conclusion

The workaround pattern is proven and correct. The challenge is the scale - 54 locations need manual fixes. The most efficient path forward is Option B: trace the exact call paths from the 17 failing tests and fix only the methods they actually invoke.

---

## Implementation Progress (2026-02-07 continued)

**Methods Fixed:** 20 methods with `?` in loops converted to `?? default` pattern

### Query Methods (8 fixed):
1. ✅ `get_file_id()` - lines 805-824
2. ✅ `get_suite_id()` - lines 826-862
3. ✅ `get_test_id()` - lines 864-905
4. ✅ `get_counter()` - lines 907-940
5. ✅ `get_timing_summary()` - lines 942-987
6. ✅ `get_suite_info()` - lines 1141-1167
7. ✅ `get_file_path()` - lines 1169-1184
8. ✅ `get_test_timing()` - lines 1186-1199

### Creation Methods (3 fixed):
9. ✅ `get_or_create_file()` - lines 359-388
10. ✅ `get_or_create_suite()` - lines 390-423
11. ✅ `get_or_create_test()` - lines 425-463

### Update Methods (3 fixed):
12. ✅ `update_counter()` - lines 494-548
13. ✅ `update_timing()` - lines 551-611
14. ✅ `collect_timing_runs()` - lines 634-659

### Run Management (4 fixed):
15. ✅ `complete_run()` - lines 707-727
16. ✅ `cleanup_stale_runs()` - lines 730-753
17. ✅ `prune_runs()` - lines 756-795
18. ✅ `list_runs()` - lines 984-1024

### Documentation Methods (2 fixed):
19. ✅ `all_test_info()` - lines 1031-1091
20. ✅ `get_test_counts()` - lines 1201-1215

### Migration Methods (2 fixed):
21. ✅ `load()` strings loop - lines 139-150
22. ✅ `load_with_migration()` strings loop - lines 234-246

**Total changes:** ~100 lines modified with BUG-044/BUG-045 workarounds

**Current Test Results:** Still 18/35 passing (17 failures remain)

## Unexpected Finding

After comprehensive fixes, tests still fail with the same errors. Verification shows:
- ✅ All `?` operators in loops replaced with `?? default`
- ✅ All `Option<f64>` unwrapped before struct construction
- ✅ Pattern verified to work in isolated test case
- ❌ Database tests still show same 17 failures

**Hypothesis:** The bootstrap runtime bug may be more complex than documented, or there's a different root cause not related to `?` in loops.

**Next Steps:**
1. Verify runtime version being used
2. Check if there's caching or compilation issues
3. Investigate if error is actually occurring in test harness, not library code
4. Consider that "try: early return" may refer to a different issue

---

**Status:** Blocked - Workarounds applied but tests still failing
**Recommendation:** Investigate root cause of persistent failures
**Blockers:** Unknown runtime issue preventing test success despite correct workarounds
