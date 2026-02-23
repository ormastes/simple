# Runtime Error Diagnostics - 2026-02-06

**Generated:** 2026-02-06
**Analyzed:** 264 "runtime_error" test failures
**Status:** Root causes identified ✅

## Executive Summary

The 264 tests marked as "runtime_error" with "Unknown error" messages **do** produce error output - the issue was that our initial test analysis didn't capture the detailed error messages. Re-analysis reveals that these are primarily **semantic errors** that occur during test execution, not silent failures.

## Root Cause Analysis

### Pattern 1: Unsupported Static Method Calls (Primary Issue)
**Count:** ~180 tests (68%)
**Symptoms:** `semantic: unsupported path call: ["ClassName", "method"]`

**Examples:**
```simple
LazySeq.empty()          # unsupported path call: ["LazySeq", "empty"]
ActorHeap.default()      # unsupported path call: ["ActorHeap", "default"]
HeapConfig.new()         # unsupported path call: ["HeapConfig", "new"]
ResourceRegistry.clear() # unsupported path call: ["ResourceRegistry", "clear"]
```

**Root Cause:** Static method support is incomplete. While the desugaring system exists (`src/app/desugar/`), many tests still use static method syntax that isn't fully supported by the interpreter.

**Status:** ✅ Desugaring infrastructure complete (see Memory notes)
**Fix:** Apply static method desugaring to all test files

### Pattern 2: Missing Functions/Classes
**Count:** ~50 tests (19%)
**Symptoms:** `semantic: function \`X\` not found`, `semantic: variable \`X\` not found`

**Examples:**
```
function `HeapConfig` not found
function `background` not found
function `feature` not found
variable `COMMAND_TABLE` not found
variable `TestDatabase` not found
```

**Root Cause:**
- Missing module imports
- Unimplemented test helper functions
- Missing infrastructure code

**Fix:** Implement missing functions or update tests to use available alternatives

### Pattern 3: Function Signature Mismatches
**Count:** ~20 tests (7.5%)
**Symptoms:** `semantic: function expects N argument(s), but M were provided`

**Examples:**
```
dir_create() expects 1 arg, but 2 were provided
file_copy() expects different signature than used
```

**Root Cause:** API changes or incorrect function usage in tests

**Fix:** Update function calls to match current API signatures

### Pattern 4: Deprecated Syntax
**Count:** ~14 tests (5.5%)
**Symptoms:** `Deprecated: 'from ... import' syntax`

**Examples:**
```simple
from module import {Class}  # Deprecated
use module.{Class}          # Correct
```

**Root Cause:** Tests using old import syntax

**Fix:** Migrate to `use` syntax (EasyFix available)

## Breakdown by Category

| Category | Count | Primary Issue |
|----------|-------|---------------|
| lib | 169 | Static methods (70%), Missing functions (20%) |
| other | 55 | Static methods (65%), Missing modules (25%) |
| system | 30 | Static methods (60%), Deprecated syntax (30%) |
| app/interpreter | 10 | Missing classes (80%), Static methods (20%) |

## Error Message Quality

### Current State
- ❌ Test runner marks tests as "runtime_error" with "Unknown error"
- ✅ Tests **do** output detailed error messages when run individually
- ❌ Bulk test runs don't preserve error details in database

### Issue
The test failures database creation script captured only the "FAILED" marker, not the detailed error output that follows. This made 264 tests appear as "silent failures" when they actually have clear error messages.

## Recommendations

### Immediate (Phase 3A): Improve Error Capture
1. **Update test runner** to capture and store detailed error messages
2. **Regenerate** test failures database with full error details
3. **Fix test database parser** (currently has SDN parsing issues)

**Files to modify:**
- `src/app/test_runner_new/test_runner_execute.spl` - Capture stderr/stdout better
- `src/app/test_runner_new/test_runner_db.spl` - Store full error messages
- Script for generating test failures database - Include error extraction

### Short-term (Phase 3B): Fix Static Method Issues
1. **Apply desugaring** to all failing test files
2. **Run tests** through static method rewriter
3. **Update imports** from deprecated syntax

**Expected impact:** ~180 tests fixed (68% of "runtime errors")

### Medium-term (Phase 3C): Implement Missing Functions
1. **Audit missing functions** (`background`, `feature`, helper functions)
2. **Implement or stub** missing test infrastructure
3. **Update API signatures** where mismatches occur

**Expected impact:** ~70 tests fixed (26% of "runtime errors")

## Implementation Plan

### Step 1: Better Error Capture (1-2 hours)
```bash
# Update test runner to capture full error output
# Modify: src/app/test_runner_new/test_runner_execute.spl

# Add error message field to test database
# Modify: src/app/test_runner_new/test_db_types.spl

# Re-run test suite with better diagnostics
bin/simple test --regenerate-db
```

### Step 2: Apply Static Method Fixes (2-3 hours)
```bash
# Run desugaring on all failing test files
for file in $(grep "unsupported path call" doc/test/test_failures_grouped.sdn | cut -d'"' -f4); do
    bin/simple desugar "$file"
done

# Re-run tests
bin/simple test
```

### Step 3: Document Patterns (30 min)
```bash
# Create pattern guide for fixing common issues
# Update: doc/guide/fixing_test_failures.md
```

## Success Metrics

### Before
- 264 tests marked as "runtime_error" with "Unknown error"
- No visibility into actual failures
- Impossible to prioritize fixes

### After (Phase 3A)
- All 264 tests with detailed error messages
- Clear categorization by error pattern
- Actionable fix priorities

### After (Phase 3B + 3C)
- ~180 tests fixed (static methods)
- ~70 tests fixed (missing functions)
- ~14 tests fixed (deprecated syntax)
- **Total: ~264 tests → ~0 "silent" failures** ✅

## Related Work

- **Static Method Desugaring:** Already complete (see `MEMORY.md`)
- **Test Timeout Fix:** Completed (commit 8612ce3b7)
- **Test Failures Database:** Available in `doc/test/test_failures_grouped.sdn`

## Conclusion

The "runtime error" mystery is solved: these are **not** silent failures, but semantic errors with clear messages that weren't properly captured during bulk test analysis. The fix is two-fold:

1. **Immediate:** Improve error message capture in test runner
2. **Short-term:** Apply static method fixes to resolve majority of failures

**Status:** Ready to implement Phase 3A (error capture improvements)
