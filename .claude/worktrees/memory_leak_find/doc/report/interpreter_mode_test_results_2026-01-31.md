# Interpreter Mode Test Results - 2026-01-31

## Summary

Tested Simple language build using the Simple CLI (`./bin/wrappers/simple test`) and identified several issues in interpreter mode tests.

## Issues Found

### 1. ✅ FIXED: FFI Function Export Warnings
**Status:** Fixed in previous session
**Location:** `src/app/test_runner_new/test_runner_types.spl`
**Issue:** Attempting to export `extern fn` declarations
**Resolution:** Removed invalid export statements

### 2. 🔴 CRITICAL: Nested Method Mutation Not Detected
**Status:** Active Bug - Needs Rust Interpreter Fix
**Location:** Interpreter nested method call handling
**Symptoms:**
```
[DEBUG NESTED METHOD] self.instructions.push() fell through to non-mutating path
semantic: array index out of bounds: index is 0 but length is 0
```

**Root Cause:**
When a `me` (mutable) method calls a mutating method on a field (e.g., `self.instructions.push()`), the interpreter doesn't properly detect this as a mutation chain. The modifications don't persist.

**Example from `src/compiler/backend/mir_test_builder.spl:62`:**
```simple
class MirTestBuilder:
    instructions: List<text> = []

    me add_const_int(dest: i32, value: i64):
        self.instructions.push("const_int v{dest} = {value}")  # ❌ Not persisting
        if dest >= self.next_vreg:
            self.next_vreg = dest + 1
```

**Impact:**
- 15 out of 117 backend tests failing (13% failure rate)
- All failures related to MIR test builder instruction tracking
- Tests in `test/compiler/backend/`:
  - `instruction_coverage_spec.spl` - Parse error + mutation issues  - `backend_capability_spec.spl` - Mutation issues
  - `differential_testing_spec.spl` - Mutation issues
  - `exhaustiveness_validator_spec.spl` - Mutation issues
  - `backend_basic_spec.spl` - 9/18 tests failing due to mutation
  - `native_ffi_spec.spl` - Mutation issues
  - `native_bridge_spec.spl` - Mutation issues

**Failed Tests:**
```
FAIL  test/compiler/backend/instruction_coverage_spec.spl (parse error)
FAIL  test/compiler/backend/backend_capability_spec.spl
FAIL  test/compiler/backend/differential_testing_spec.spl
FAIL  test/compiler/backend/exhaustiveness_validator_spec.spl
FAIL  test/compiler/backend/backend_basic_spec.spl (9 failed)
FAIL  test/compiler/backend/native_ffi_spec.spl
FAIL  test/compiler/backend/native_bridge_spec.spl

PASS  test/compiler/backend/mir_instruction_complete_spec.spl (16 passed)
PASS  test/compiler/backend/sspec_system_test_spec.spl (18 passed)
PASS  test/compiler/backend/mir_builder_intensive_spec.spl (59 passed)
```

**Workaround Options:**
1. **Temporary:** Modify MirTestBuilder to use explicit reassignment:
   ```simple
   me add_const_int(dest: i32, value: i64):
       val new_list = self.instructions
       new_list.push("const_int v{dest} = {value}")
       self.instructions = new_list
   ```

2. **Proper Fix:** Update Rust interpreter in `rust/compiler/src/interpreter/expr.rs`
   to properly track mutation chains through field method calls.

### 3. ⚠️  Parse Error in instruction_coverage_spec.spl
**Status:** To Be Investigated
**Error:** `parse error: Unexpected token: expected pattern, found Vec`
**Location:** `test/compiler/backend/instruction_coverage_spec.spl`
**Note:** File doesn't contain "Vec" string - may be an internal parser error

### 4. ⚠️  Deprecation Warnings
**Status:** Non-Critical
**Examples:**
- `import` keyword deprecated (use `use` instead)
- `None` should be `nil`

**Affected Files:**
- Multiple test files using `import std.spec` instead of `use std.spec.*`
- Test files using `None` instead of `nil`

### 5. ⚠️  Database Lock Contention
**Status:** Non-Critical
**Message:** `Failed to acquire lock: Timeout`
**Impact:** Test run tracking disabled, but tests still execute correctly

## Test Results Summary

### Unit Tests
**Status:** ✅ PASSING
- `test/unit/spec/expect_spec.spl`: 21/21 passed (28ms)
- `test/unit/spec/progress_spec.spl`: 14/14 passed (17ms)
- `test/unit/spec/registry_spec.spl`: 14/14 passed (6ms)

**Total:** 4 files, all passed

### Integration Tests
**Status:** ✅ PASSING
- `test/integration/todo_parser_cli_test.spl`: 3/3 tests
**Total:** 3 tests passed

### Interpreter Sample Tests
**Status:** ✅ PASSING
- `test/system/interpreter/sample/python_inspired_sample/variables_assignment_spec.spl`: 7/7 passed (3ms)
**Total:** All Python-inspired samples passing

### Backend Compiler Tests
**Status:** 🔴 PARTIAL FAILURE
- **Total:** 117 tests
- **Passed:** 102 (87%)
- **Failed:** 15 (13%)
- **Time:** 649ms

**Passing Tests:**
- `mir_instruction_complete_spec.spl`: 16 passed (32ms)
- `sspec_system_test_spec.spl`: 18 passed (11ms)
- `mir_builder_intensive_spec.spl`: 59 passed (67ms)

**Failing Tests:** See Issue #2 above

## Runtime Status

### Build
- ✅ Rust build: Clean (6.05s)
- ✅ Full build: Clean (2m 59s)
- ✅ No compiler warnings

### Test Discovery
- ✅ 542 test files found
- ✅ Test runner working correctly
- ✅ FFI functions operational (all 11 verified)

### Simple CLI (`./bin/wrappers/simple`)
- ✅ Runs Simple app code (`src/app/cli/main.spl`)
- ✅ Test command working
- ✅ Help system working
- ✅ Version display working

## Recommendations

### Immediate Actions
1. **Fix nested method mutation tracking** (Rust interpreter bug)
   - Location: `rust/compiler/src/interpreter/expr.rs`
   - Add proper mutation chain detection for `self.field.method()` patterns
   - This will fix 15 failing backend tests

2. **Investigate parse error** in instruction_coverage_spec.spl
   - Check for internal parser state issues
   - May be related to enum variant parsing

3. **Clean up debug logging**
   - Remove "[DEBUG NESTED METHOD]" messages from production output
   - Keep in debug build only

### Non-Critical Improvements
1. Fix deprecation warnings (update `import` to `use`, `None` to `nil`)
2. Resolve database lock contention in test runner
3. Update test files to use Simple idioms (avoid `.new()`, use direct construction)

## Conclusion

**Overall Status:** 🟡 Mostly Working with Known Issues

The Simple language runtime and CLI are functional. Most tests pass successfully (87% in backend tests, 100% in unit/integration tests). The main issue is a bug in the interpreter's handling of nested method mutations, which affects MIR test builder functionality. This is a known issue with a clear path to resolution.

**Ready for Use:** Yes, for features not dependent on nested mutable method chains.
**Blocker for Full Adoption:** Nested method mutation bug must be fixed.
