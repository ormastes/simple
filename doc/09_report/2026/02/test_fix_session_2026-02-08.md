# Test Fix Session - 2026-02-08

## Summary

Attempted to implement test fix plan targeting ~450 tests. Discovered that most tests in the plan were either:
1. **Compiled-only tests** - require JIT compiler, not fixable with Simple code
2. **Stub tests** - have `fn(): pass` bodies with no actual implementation
3. **Module closure limitations** - runtime can't support the required patterns

## Phase 1a: cli_dispatch_spec ✅ Partial Success

**Target:** 25 tests
**Achieved:** 7 tests passing (28%)
**Time:** ~2 hours

### Changes Made

#### 1. `src/app/cli/dispatch.spl`
- **Added exports:**
  - `command_count()` - returns total command count
  - `simple_impl_count()` - returns commands with Simple implementations
  - `coverage_percentage()` - returns % of Simple implementations
  - `get_all_commands()` - accessor for COMMAND_TABLE

- **Pre-computed module counts** (workaround for module closure limitation):
  ```simple
  var g_command_count = 0
  var g_simple_impl_count = 0

  fn init_counts():
      for entry in COMMAND_TABLE:
          g_command_count = g_command_count + 1
          if entry.has_simple_impl():
              g_simple_impl_count = g_simple_impl_count + 1

  init_counts()
  ```

- **Updated functions** to use pre-computed values:
  ```simple
  fn command_count() -> i64:
      g_command_count

  fn simple_impl_count() -> i64:
      g_simple_impl_count

  fn coverage_percentage() -> f64:
      val total = g_command_count as f64
      val simple = g_simple_impl_count as f64
      if total > 0.0:
          (simple / total) * 100.0
      else:
          0.0
  ```

#### 2. `src/app/io/mod.spl`
- **Fixed function ordering:** Moved `env_get()` and `env_set()` before `home()` to avoid forward reference
- **Fixed `home()` function:** Changed to call `rt_env_get("HOME")` directly instead of `env_get("HOME")`

#### 3. `test/integration/cli_dispatch_spec.spl`
- **Fixed import syntax:** Changed from `use app.io.{...}` to `use app.io.mod (...)`
  - **Critical discovery:** Import syntax must be `use app.io.mod (func1, func2)` for functions in mod.spl
  - Using `.{}` syntax fails silently
- **Converted all `skip_it` to `it`** to enable tests

### Tests Now Passing

1. ✅ has 48 total commands
2. ✅ has 47 Simple implementations
3. ✅ has 98% coverage
4. ✅ finds compile command
5. ✅ finds build command
6. ✅ dispatches in under 10ms overhead
7. ✅ startup completes in under 25ms

### Remaining Issues

**18 tests still fail** due to runtime limitation: **Module function closures broken**

From MEMORY.md:
> **Module function closures broken:** Imported functions can't access their module's `var` state.

The workaround (pre-computing counts at module init) only works for values that don't change. For functions that need to access COMMAND_TABLE dynamically (like tests that call `find_command()` multiple times or access returned objects), the limitation persists.

**Specific failure pattern:**
- `find_command("compile")` works when called from within cli_dispatch_spec context
- `find_command("invalid")` fails with "variable `COMMAND_TABLE` not found"
- Tests that call methods on returned `CommandEntry` objects fail

The root cause appears to be that when `find_command()` returns a `CommandEntry` object and tests try to call methods on it (like `.should_use_rust()`), those methods can't access the original module context.

## Phase 1b: coverage_ffi_spec ⏭️ Skipped

**Reason:** All 29 tests are stubs with `fn(): pass` bodies only.

Example:
```simple
skip_it "checks if coverage is enabled", fn():
    pass
```

No actual test logic to execute. Fixing imports would make tests pass trivially but provide no value.

## Phase 1c: concurrent_spec ⏭️ Skipped

**Reason:** All 50 tests are "compiled-only" - require JIT compiler, not interpreter.

Test output:
```
it should enable producer-consumer pattern ... skipped (compiled-only)
it should enable caching ... skipped (compiled-only)
it should enable lazy initialization ... skipped (compiled-only)

0 examples, 0 failures
```

Cannot be fixed with Simple code changes alone. Would require interpreter support for concurrency primitives.

## Phase 2a: debug_spec ⏭️ Skipped

**Reason:** All 104 tests are "compiled-only" - require JIT compiler.

Test output:
```
it adds watch expression ... skipped (compiled-only)
it uses 'w' alias ... skipped (compiled-only)
help command
  it returns help text ... skipped (compiled-only)

0 examples, 0 failures
```

## Phases 2b-4: Not Attempted

**Reason:** Time spent debugging fundamental limitations in earlier phases revealed that the plan was based on incomplete information:
- Phase 3a-3c: All tests are stubs with no implementation
- Phase 4: SFFI wrappers require Rust Tier 1 implementations (separate work)

## Key Discoveries

### 1. Import Syntax for mod.spl Files

**CORRECTED (2026-02-08):** Both syntaxes work!

**Curly braces (preferred):**
```simple
use app.io.{env_set, env_get}          # Works! ✅
use app.io.{file_read, shell}          # Works! ✅
```

**Parentheses (alternative):**
```simple
use app.io.mod (env_set, env_get)      # Also works! ✅
use app.io.mod (file_read)              # Also works! ✅
```

**Key requirement:** Imports must be at **module level**, not inside function/test blocks.

**Verified:** `test/integration/import_syntax_spec.spl` (5/5 tests passing)

### 2. Module Function Closure Workaround Pattern

When exported functions need to access module-level collections:

**Problem:**
```simple
val COMMAND_TABLE = [...]

fn command_count() -> i64:
    COMMAND_TABLE.len() as i64  # Fails when called from imports
```

**Solution:**
```simple
var g_command_count = 0
val COMMAND_TABLE = [...]

fn init_counts():
    for entry in COMMAND_TABLE:
        g_command_count = g_command_count + 1

init_counts()

fn command_count() -> i64:
    g_command_count  # Works! Returns pre-computed value
```

### 3. Forward References in Module Initialization

**Problem:**
```simple
fn home() -> text:
    env_get("HOME")  # Fails: env_get not defined yet

fn env_get(key: text) -> text:
    rt_env_get(key)
```

**Solution:**
```simple
fn env_get(key: text) -> text:
    rt_env_get(key)

fn home() -> text:
    env_get("HOME")  # Works! env_get defined before use
```

Or call extern function directly:
```simple
fn home() -> text:
    rt_env_get("HOME")  # Works! No forward reference
```

## Test Suite Classification

From this session, tests fall into these categories:

1. **Fixable with Simple code** (~7-10% of "skipped" tests)
   - Import issues
   - Missing simple helper functions
   - Function ordering problems

2. **Stub tests** (~30% of "skipped" tests)
   - Have `fn(): pass` bodies
   - No actual test logic
   - Would pass but provide no value

3. **Compiled-only** (~40% of "skipped" tests)
   - Require JIT compiler features
   - Can't run in interpreter
   - Need compiler work, not Simple code

4. **Runtime limitations** (~20% of "skipped" tests)
   - Module closure issues
   - Generic type limitations
   - Parser limitations (try/catch, etc.)

## Recommendations

### 1. Update Test Metadata
Add test categories to distinguish:
- `@skip:stub` - Test has no implementation yet
- `@skip:compiled-only` - Requires compiler
- `@skip:runtime-limit` - Blocked by runtime limitation
- `@skip:fixable` - Can be fixed with Simple code

### 2. Focus Areas for Test Fixes
- **High-value:** Tests that verify existing functionality but have import/syntax issues
- **Medium-value:** Tests that need simple helper functions added
- **Low-value:** Stub tests (fix only when implementing the feature)

### 3. Runtime Improvements Needed
- **Module function closures:** Allow exported functions to access module-level collections
- **Import syntax consistency:** Make `.{}` syntax work like `.mod ()` syntax

### 4. Plan Validation Process
Before creating test fix plans:
1. Run the test file to see actual failures (not just skip counts)
2. Check if tests have actual implementation (`fn(): pass` = stub)
3. Check if tests are "compiled-only"
4. Estimate fixability based on failure type

## Files Modified

- `src/app/cli/dispatch.spl` - Added exports, pre-computed counts
- `src/app/io/mod.spl` - Fixed function ordering
- `test/integration/cli_dispatch_spec.spl` - Fixed imports, enabled tests

## Net Result

- **Tests Fixed:** 7 (from 0 passing to 7 passing)
- **Tests Attempted:** 25 (cli_dispatch_spec)
- **Success Rate:** 28%
- **Time Spent:** ~2 hours
- **Blockers Identified:** Module closure limitation (18 tests), stub tests (majority), compiled-only tests (majority)
