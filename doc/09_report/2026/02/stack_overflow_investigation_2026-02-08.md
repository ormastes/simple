# Stack Overflow Investigation and Fix (2026-02-08)

## Summary

**Issue:** Running full test suite causes stack overflow crash
**Root Cause:** Incorrect `.?.` operator usage (existence check followed by field access)
**Status:** ✅ **Partially Fixed** - 1 of 6 files fixed
**Remaining:** 5 files with 20 instances need same fix

## Investigation Process

### Step 1: Identify Crashing File

Ran test suite with narrow focus:
```bash
bin/simple test test/app 2>&1
```

**Error:**
```
[DEBUG FIELD ACCESS] Trying to access field 'priority' on value type: "bool"
thread 'main' has overflowed its stack
fatal runtime error: stack overflow, aborting
```

**File:** `test/app/interpreter/async_runtime/actor_scheduler_spec.spl`

### Step 2: Root Cause Analysis

**Problem Pattern:**
```simple
val act = scheduler.get_actor(id)
check(act.?.priority == ActorPriority.High)  # WRONG
```

**Explanation:**
1. `act.?` checks if value is "present" → returns **boolean** (true/false)
2. `.priority` tries to access field on boolean → **ERROR**
3. Error handler recursively tries to access fields → **infinite recursion**
4. Stack overflow crash

**From MEMORY.md:**
```
- .? checks if value is "present" (not nil AND not empty)
- Returns: boolean (true/false)
- opt? and opt.? may fail - Use ?? default pattern instead
```

### Step 3: Correct Patterns

**Pattern 1: Pattern Matching (Recommended)**
```simple
val act = scheduler.get_actor(id)
match act:
    case Some(a):
        check(a.priority == ActorPriority.High)  # Correct - unwrapped
    case None:
        fail "actor not found"
```

**Pattern 2: Unwrap (When Sure it Exists)**
```simple
val act = scheduler.get_actor(id)
check(act.unwrap().priority == ActorPriority.High)
```

**Pattern 3: Null Coalescing**
```simple
val priority = (scheduler.get_actor(id) ?? default_actor).priority
check(priority == ActorPriority.High)
```

## Fix Applied

### File: actor_scheduler_spec.spl

**Instances Fixed:** 11
**Pattern:** Converted all `opt.?.field` to pattern matching

**Example Fix:**
```diff
- check(act.?.priority == ActorPriority.High)
+ match act:
+     case Some(a):
+         check(a.priority == ActorPriority.High)
+     case None:
+         fail "actor not found"
```

**Also Fixed:**
- Replaced all `None` with `nil` (2 instances)

**Results:**
- ✅ File runs without stack overflow
- ✅ 30/45 tests passing (15 failures due to other issues)
- ✅ Runtime: 176ms (was: stack overflow crash)

## Remaining Files to Fix

| File | Instances | Priority |
|------|-----------|----------|
| test/app/interpreter/helpers/debug_spec.spl | 11 | High |
| test/compiler/dim_constraints_spec.spl | 4 | Medium |
| test/app/interpreter/memory/message_transfer_spec.spl | 2 | Low |
| test/app/interpreter/memory/refc_binary_spec.spl | 2 | Low |
| test/app/interpreter/perf/perf_spec.spl | 1 | Low |
| **Total** | **20** | |

### Locations in debug_spec.spl

```
Line 384: expect bp.?.enabled
Line 385: expect bp.?.hit_count == 0
Line 386: expect bp.?.condition == Some("x > 0")
Line 397: expect bp.?.condition == nil
Line 753: expect frame.?.fn_name == "main"
Line 754: expect frame.?.file == "test.spl"
Line 755: expect frame.?.line == 42
Line 766: expect frame.?.fn_name == "fn3"
Line 767: expect frame.?.line == 3
Line 932: expect bp.?.hit_count == 1
Line 963: expect bp.?.hit_count == 3
```

### Locations in Other Files

**dim_constraints_spec.spl (4 instances):**
- Lines unknown - need grep analysis

**message_transfer_spec.spl (2 instances):**
- Lines unknown - need grep analysis

**refc_binary_spec.spl (2 instances):**
- Lines unknown - need grep analysis

**perf_spec.spl (1 instance):**
- Lines unknown - need grep analysis

## Full Test Suite Status

**After actor_scheduler fix:**
- ✅ actor_scheduler_spec: Runs without crash (30/45 passing)
- ❌ Full test suite: Still crashes (different file causes it)

**Test before crash:**
```
Running: test/app/interpreter/core/symbol_spec.spl
Global interner
  ✓ provides convenience intern function
  ✓ provides convenience resolve function
  ✓ shares state across intern calls
Common symbols initialization
  ✓ pre-interns common identifiers

[CRASH] thread 'main' has overflowed its stack
```

**Note:** symbol_spec.spl doesn't have `.?.` pattern, suggesting a different root cause. Possibly `init_common_symbols()` causes infinite recursion.

## Systematic Fix Strategy

### Option 1: Manual Fix (High Quality)

Fix each file individually with pattern matching:
- Review each usage context
- Choose appropriate pattern (match vs unwrap vs ??)
- Verify logic correctness
- **Effort:** ~2 hours (11 + 4 + 2 + 2 + 1 = 20 instances)

### Option 2: Automated Find/Replace (Fast)

Create sed script to replace all instances:
```bash
# Find pattern: opt.?.field
# Replace with: match opt: case Some(x): x.field case None: fail
```

**Risk:** May break some edge cases
**Effort:** ~30 minutes + testing

### Option 3: Skip Files (Temporary)

Mark files with `skip_it` until manual fix:
- Allows full test suite to run
- Identifies other blocking issues
- Defers fix to later session

**Effort:** ~10 minutes

## Recommended Next Steps

### Short-Term (This Session)

**Option 3: Skip remaining files**
- Add skip markers to 5 remaining files
- Test if full suite runs without other crashes
- Identify any additional blocking issues
- **Time:** 10-15 minutes

**Why:** Enables full test suite analysis to find other issues quickly

### Medium-Term (Next Session)

**Option 1: Fix remaining 20 instances**
- Manual review and pattern matching
- High quality, safe fixes
- **Time:** 2 hours
- **Result:** All `.?.` patterns fixed, test suite stable

### Long-Term (Runtime Fix)

**Prevent infinite recursion in error handler**
- Add stack depth limiting
- Detect field access on wrong type earlier
- Provide better error messages (not just debug)
- **Effort:** 1-2 days runtime work

## Impact Assessment

### Before Fix
- Full test suite: **CRASH** (stack overflow)
- Analysis: **Blocked** (can't run full suite)
- CI/CD: **Broken** (tests don't complete)

### After actor_scheduler Fix
- actor_scheduler_spec: **30/45 passing** (was: crash)
- Full test suite: **Still crashes** (different file)
- Progress: **1 of 6 files fixed** (17%)

### After All Fixes (Projected)
- Remaining 5 files: **Fixed**
- Full test suite: **May still crash** (symbol_spec or other issues)
- Progress: **All .?. patterns fixed**
- **Benefit:** Eliminates one class of stack overflow causes

## Testing Verification

### Verification Steps

1. ✅ **Fixed file runs:** `bin/simple test test/app/interpreter/async_runtime/actor_scheduler_spec.spl`
   - Result: 30/45 passing, 176ms runtime

2. ⏸️ **Full suite runs:** `bin/simple test test/`
   - Result: Still crashes (different file)

3. ⏸️ **Remaining files run:** (After fix)
   - debug_spec.spl
   - dim_constraints_spec.spl
   - message_transfer_spec.spl
   - refc_binary_spec.spl
   - perf_spec.spl

## Lessons Learned

### 1. `.?` Operator Semantics

**What it does:**
- Returns **boolean** indicating presence
- NOT the same as optional chaining (`?.` in other languages)
- Can't be used before field access

**Correct usage:**
```simple
# Correct: Check presence
if opt.?:
    do_something()

# Wrong: Access field
if opt.?.field == value:  # ERROR - field on boolean
```

### 2. Pattern Matching is Safest

**Why:**
- Explicit unwrapping
- Handles None case explicitly
- Clear intent
- No risk of runtime errors

**Always prefer:**
```simple
match opt:
    case Some(x): use x
    case None: handle_none()
```

### 3. Error Cascade Can Cause Stack Overflow

**Issue:** Field access on wrong type triggers error handler, which tries to introspect the value, which may access fields, causing recursion.

**Solution:** Fix root cause (don't access fields on wrong types)

## File Modified

- ✅ `test/app/interpreter/async_runtime/actor_scheduler_spec.spl`
  - 11 instances of `.?.field` → pattern matching
  - 2 instances of `None` → `nil`
  - Result: 30/45 tests passing (was: crash)

## Files Remaining

- ⏸️ `test/app/interpreter/helpers/debug_spec.spl` (11 instances)
- ⏸️ `test/compiler/dim_constraints_spec.spl` (4 instances)
- ⏸️ `test/app/interpreter/memory/message_transfer_spec.spl` (2 instances)
- ⏸️ `test/app/interpreter/memory/refc_binary_spec.spl` (2 instances)
- ⏸️ `test/app/interpreter/perf/perf_spec.spl` (1 instance)

## Conclusion

**Root Cause Identified:** `.?.field` pattern causes field access on boolean, leading to infinite recursion in error handler.

**Fix Proven:** Pattern matching resolves the issue (actor_scheduler_spec now runs).

**Remaining Work:** 5 files with 20 instances need same fix (~2 hours).

**Blocker Status:** ⚠️ **Partially Unblocked** - Fixed 1 file, but full test suite still crashes due to other issues (likely symbol_spec.spl or subsequent files).

**Recommendation:** Apply Option 3 (skip remaining files temporarily) to identify all blocking issues, then fix systematically in next session.

---

**Status:** ✅ Investigation Complete, Partial Fix Applied
**Next:** Skip remaining 5 files, test full suite, identify other blockers
