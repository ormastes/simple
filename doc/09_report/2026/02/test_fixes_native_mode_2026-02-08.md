# Test Fixes and Native Mode Investigation - 2026-02-08

## Summary

**Objective:** Run tests in compiler native mode and fix skip/fail tests
**Outcome:** Fixed syntax issues, improved test pass rate, documented native mode limitations
**Tests Fixed:** 24 additional tests passing in control_flow_spec
**Tests Improved:** 26/31 passing in mailbox_spec (5 remaining failures due to implementation issues)

---

## Key Findings

### Native Mode Status

**Current Implementation:** Native mode (`--mode=native`) is **not fully implemented**
- Test runner shows: `[INFO] Native mode for tests not supported, using safe mode`
- Falls back to interpreter/safe mode execution
- No actual JIT compilation or native binary generation occurs

**Test Mode Options:**
```bash
bin/simple test --mode=interpreter  # Default: interpreter mode
bin/simple test --mode=smf          # SMF bytecode mode (if .smf files exist)
bin/simple test --mode=native       # Currently falls back to interpreter
```

**Code Location:** `src/app/test_runner_new/test_runner_execute.spl`
- Lines 357-373: `run_test_file_native()` - just runs through interpreter
- Line 267-355: `preprocess_sspec_file()` - wraps SSpec files in `fn main()` (unused)

### Syntax Issues Fixed

#### 1. Match Expression Syntax (`=>` → `case:`)

**Issue:** Tests using Rust/Scala-style match syntax (`=>`) instead of Simple syntax (`case:`)

**Fixed File:** `test/app/interpreter/control/control_flow_spec.spl`
- **Before:**
  ```simple
  val result = match t:
      (1, x) => x * 10
      _ => 0
  ```
- **After:**
  ```simple
  val result = match t:
      case (1, x): x * 10
      case _: 0
  ```

**Tests Fixed:** 24 tests in control_flow_spec now passing (was showing syntax errors)

#### 2. None → nil Convention

**Issue:** Python-style `None` used instead of Simple's `nil`

**Fixed File:** `test/app/interpreter/async_runtime/mailbox_spec.spl`
- **Before:** `MessageRef.new(1, None, MessagePriority.Normal, 100, 0)`
- **After:** `MessageRef.new(1, nil, MessagePriority.Normal, 100, 0)`

**Impact:** All `None` references (4 occurrences) replaced with `nil`

---

## Test Results

### ✅ Passing Tests

| Spec File | Tests | Status | Duration |
|-----------|-------|--------|----------|
| `test/app/interpreter/control/control_flow_spec.spl` | 24/24 | ✅ PASS | 34ms |
| `test/runtime/runtime_parser_bugs_spec.spl` | 22/22 | ✅ PASS | 268ms |
| `test/integration/cli_dispatch_spec.spl` | 25/25 | ✅ PASS | 295ms |
| `test/app/build/link_bins_spec.spl` | 5/5 | ✅ PASS | 11ms |
| `test/app/interpreter/core/symbol_spec.spl` | 14/14 | ✅ PASS | - |

**Total Verified Passing: 90 tests**

### ⚠️ Partially Fixed

| Spec File | Tests | Status | Duration |
|-----------|-------|--------|----------|
| `test/app/interpreter/async_runtime/mailbox_spec.spl` | 26/31 | ⚠️ 5 FAIL | 97ms |

**Remaining Failures in mailbox_spec:**
1. `drops stale messages` - `expected false to equal true`
2. `tracks drop rate` - `expected false to equal true`
3. Three other failures (implementation-related, not syntax)

These failures appear to be actual bugs in the mailbox implementation, not test issues.

### ⏭️ Skipped Tests

**Total Skipped:** 203+ tests with `skip_it` or `slow_it`

**Categories:**
- **Debug module tests:** All tests in `test/app/interpreter/helpers/debug_spec.spl` skipped (module dependencies unavailable)
- **System feature tests:** Most tests in `test/system/features/` marked `# @pending`
- **Slow tests:** Integration tests marked with `slow_it` (run with `--only-slow`)

**Example Skipped Directories:**
- `test/system/features/actors/`
- `test/system/features/async_effects/`
- `test/system/features/generics/`
- `test/system/features/futures_promises/`

---

## Common Test Anti-Patterns Found

### 1. Match Expressions with `=>`

**Pattern:** Using `=>` instead of `case:` in match expressions

**How to Fix:**
```simple
# Wrong (Rust/Scala style)
match value:
    Some(x) => x * 2
    _ => 0

# Correct (Simple style)
match value:
    case Some(x): x * 2
    case _: 0
```

### 2. Using `None` Instead of `nil`

**Pattern:** Python-style `None` instead of Simple's `nil`

**How to Fix:**
```simple
# Wrong (Python style)
val x = None
fn foo() -> Option<T>: None

# Correct (Simple style)
val x = nil
fn foo() -> Option<T>: nil
```

### 3. Lambda Syntax Confusion

**Pattern:** Using `=>` for lambdas instead of `\` and `:`

**How to Fix:**
```simple
# Wrong (JavaScript/TypeScript style)
val add = (a, b) => a + b

# Correct (Simple style)
val add = \a, b: a + b
```

---

## Known Issues & Limitations

### Runtime Limitations (from MEMORY.md)

1. **NO EXCEPTIONS:** `try`/`catch`/`throw` not supported
2. **NO multi-line boolean:** Use intermediate variables
3. **NO generics in runtime parser:** Generic code is compiled-only
4. **Closure variable capture broken:** Functions can READ but not MODIFY outer variables
5. **Module function closures broken:** Imported functions can't access module's `var` state

### Parser Issues

1. **Stack Overflow:** Running all tests causes stack overflow (seen during broad test run)
2. **Module parsing limits:** 3+ `while` loops in a module causes parse failure

---

## Recommendations

### For Test Suite Maintenance

1. **Run syntax checker regularly:**
   ```bash
   # Check for common syntax issues
   grep -r "=> " test/ --include="*_spec.spl" | grep -v "# =>"
   grep -r "\bNone\b" test/ --include="*_spec.spl"
   ```

2. **Fix remaining match expressions:** There may be more files with `=>` syntax
   ```bash
   # Find all match expressions with =>
   grep -r "^\s*[^#]*=>" test/ --include="*_spec.spl"
   ```

3. **Enable skipped tests incrementally:** Focus on tests without external dependencies

### For Native Mode Implementation

1. **Implement actual JIT compilation:** Current `run_test_file_native()` doesn't compile
2. **Use `preprocess_sspec_file()`:** Already written but not used
3. **Support compilation flags:** `--backend=cranelift` / `--backend=llvm`

### For Skipped Tests

1. **Categorize skip reasons:**
   - External dependencies unavailable
   - Feature not yet implemented
   - Runtime limitations
   - Performance (slow_it)

2. **Create migration plan:** Convert `skip_it` to working tests systematically

---

## Test Execution Guide

### Run Tests by Mode

```bash
# Default interpreter mode
bin/simple test

# Explicitly set interpreter mode
bin/simple test --mode=interpreter

# Native mode (currently falls back to interpreter)
bin/simple test --mode=native

# SMF bytecode mode (if .smf files exist)
bin/simple test --mode=smf

# Safe mode with resource limits
bin/simple test --safe-mode
```

### Run Tests by Category

```bash
# Quick test (skip database writes)
bin/simple test --quick

# Unit tests only
bin/simple test --unit

# Integration tests only
bin/simple test --integration

# Slow tests only
bin/simple test --only-slow

# Skipped tests only
bin/simple test --only-skipped

# Specific file
bin/simple test test/app/interpreter/control/control_flow_spec.spl
```

### Test Filtering

```bash
# By tag
bin/simple test --tag=integration

# Fail fast (stop on first failure)
bin/simple test --fail-fast

# List tests without running
bin/simple test --list

# Show tags
bin/simple test --show-tags
```

---

## Metrics

### Tests Fixed in This Session

- **Syntax errors fixed:** 2 files (control_flow_spec, mailbox_spec)
- **Tests now passing:** +24 (control_flow_spec)
- **Tests improved:** mailbox_spec 26/31 (was 21/31)
- **Files verified passing:** 5 spec files, 90+ tests

### Overall Test Suite Status (from MEMORY.md)

- **Total spec files:** 458
- **Fully passing files:** 324 (0 failures)
- **Files with failures:** 130
- **Tests passing:** 3,606/4,379 (82% pass rate)
- **Tests failing:** 773

### Test Classification (from MEMORY.md)

- **Fixable (~10%):** Import issues, missing helpers, function ordering
- **Stub tests (~30%):** Have `fn(): pass` bodies, no actual logic
- **Compiled-only (~40%):** Require JIT compiler, can't run in interpreter
- **Runtime limits (~20%):** Module closure, generics, parser limitations

---

## Next Steps

1. **✅ DONE:** Fix match expression syntax (`=>` → `case:`)
2. **✅ DONE:** Fix `None` → `nil` conversions
3. **TODO:** Search for remaining syntax issues across all test files
4. **TODO:** Investigate mailbox_spec failures (5 tests)
5. **TODO:** Document actual native mode implementation requirements
6. **TODO:** Create plan to enable more skip_it tests

---

## Files Modified

1. `test/app/interpreter/control/control_flow_spec.spl`
   - Fixed 3 match expressions (6 cases)
   - All 24 tests now passing

2. `test/app/interpreter/async_runtime/mailbox_spec.spl`
   - Replaced 4 `None` with `nil`
   - 26/31 tests passing (5 failures remain)

---

## References

- **Test Runner:** `src/app/test_runner_new/test_runner_main.spl`
- **Test Execution:** `src/app/test_runner_new/test_runner_execute.spl`
- **Test Arguments:** `src/app/test_runner_new/test_runner_args.spl`
- **Memory Notes:** `.claude/projects/-home-ormastes-dev-pub-simple/memory/MEMORY.md`
- **CLAUDE.md:** `/home/ormastes/dev/pub/simple/CLAUDE.md`
