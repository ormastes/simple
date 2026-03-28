# Mock Test Infrastructure Issues

**Date:** 2026-01-24
**Status:** Investigation Complete

## Summary

The mock_phase3_spec.spl and related mock tests are failing due to fundamental limitations in the Simple language's module import system and function type handling.

## Issues Identified

### 1. Module Import Cannot Access Static Methods

**Problem:** When importing a module with `use testing.mocking as mocking`, accessing `mocking.Matcher.gt(5)` fails with:
```
error: undefined field: unknown property, key, or method 'Matcher' on Dict
```

**Root Cause:** The module import system returns modules as `Dict` objects. Class exports become `Constructor` values, but static method access via `module.Class.staticMethod()` is not supported.

**Workaround:** Define classes locally in the test file (as mock_spec.spl does).

### 2. Function Field Access Pattern

**Problem:** `self.matches_fn(arg)` where `matches_fn` is a function-typed field fails with:
```
error: method `matches_fn` not found on type `Matcher`
```

The interpreter treats `self.matches_fn(arg)` as a method call, not field access + invocation.

**Workaround:** Separate field access from invocation:
```simple
fn matches(arg: text) -> bool:
    val fn_ref = self.matches_fn  # Get function reference
    fn_ref(arg)                    # Call it
```

**Status:** Fix applied to mocking.spl line 228-230.

### 3. nil vs None Confusion

**Problem:** Functions returning `Option<T>` used `return nil` instead of `return None`.

**Root Cause:** `nil` and `None` are different in Simple:
- `nil` is the absence of any value (like JavaScript's `null`)
- `None` is the `Option::None` variant

**Fix Applied:**
- mocking.spl line 264: `return None` (was `return nil`)
- mocking.spl line 294: `return None` (was `return nil`)

## Affected Test Files

| File | Status | Issue |
|------|--------|-------|
| mock_phase3_spec.spl | Blocked | Module import (Issue #1) |
| mock_phase4_spec.spl | Blocked | Parse errors + Module import |
| mock_phase5_spec.spl | Blocked | Parse errors + Module import |
| mock_verification_spec.spl | Blocked | Parse errors |
| helpers_spec.spl | Blocked | Parse errors |

## Recommendations

### Short-term (Workarounds)
1. Rewrite mock tests to define classes locally (like mock_spec.spl)
2. Use direct construction `ClassName(field: value)` instead of `ClassName.new()`
3. Use separate field access for function fields

### Long-term (Requires Interpreter Changes)
1. Support `module.Class.staticMethod()` pattern in module import system
2. Support direct function field invocation `self.func_field(args)`
3. Consider unifying `nil` and `None` semantically

## Debug Output Cleanup

During investigation, several debug `eprintln!` statements were removed from hot paths:
- `src/rust/compiler/src/interpreter_call/mod.rs` (lines 314-319)
- `src/rust/compiler/src/interpreter_method/mod.rs` (line 339)
- `src/rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs` (lines 86, 244-249, 274-276)
- `src/rust/compiler/src/interpreter_module/module_loader.rs` (lines 128, 132, 136, 146, 176, 180)
- `src/rust/compiler/src/interpreter_eval.rs` (line 718)

These were causing excessive output and performance degradation during test runs.

## Test Results After Fixes

Working (mock_spec.spl): 27 examples, 0 failures
Blocked (mock_phase3_spec.spl): Cannot run due to module import limitation

## References

- `/home/ormastes/dev/pub/simple/simple/std_lib/src/testing/mocking.spl` - Mock library
- `/home/ormastes/dev/pub/simple/simple/std_lib/test/unit/testing/mock_spec.spl` - Working tests (local definitions)
- `/home/ormastes/dev/pub/simple/simple/std_lib/test/unit/testing/mock_phase3_spec.spl` - Blocked tests (module imports)
