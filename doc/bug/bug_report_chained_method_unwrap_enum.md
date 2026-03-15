# Bug Report: Chained Method Call on Unwrapped Enum Fails in Interpreter

**Bug ID:** INTERP-CHAIN-001
**Date:** 2026-03-15
**Severity:** P2 (workaround available, affects ergonomics)
**Component:** Interpreter
**Status:** Confirmed (compiled runtime — requires re-bootstrap to fix)

## Summary

Calling a method on the result of `.unwrap()` when the unwrapped value is an enum fails with `semantic: method 'to_text' not found on value of type enum in nested call context`. The interpreter loses the concrete enum type information when resolving chained method calls through `.unwrap()`.

## Minimal Reproduction

```simple
use compiler.common.config.{TypeDefault}

# FAILS:
val result = TypeDefault.from_text("i32")    # returns TypeDefault?
expect(result.unwrap().to_text()).to_equal("i32")
# Error: semantic: method 'to_text' not found on value of type enum in nested call context

# WORKS (intermediate variable):
val result = TypeDefault.from_text("i32")
val td = result.unwrap()
expect(td.to_text()).to_equal("i32")
```

## Root Cause Analysis

The interpreter's method resolution for chained calls does not propagate the concrete enum type through `.unwrap()`. When `Optional<TypeDefault>.unwrap()` returns the inner value, the interpreter tags it as generic `enum` rather than `TypeDefault`, so the subsequent `.to_text()` lookup fails.

This is a specific instance of the broader "chained methods broken" limitation documented in the language, but uniquely triggered by the `unwrap → enum method` chain.

**Relevant source:** Interpreter method dispatch / optional unwrap handling

## Observed Behavior

| Expression | Expected | Actual |
|------------|----------|--------|
| `result.unwrap().to_text()` | `"i32"` | Error: method 'to_text' not found on value of type enum |
| `val td = result.unwrap(); td.to_text()` | `"i32"` | `"i32"` (works) |

## Impact

- Forces intermediate variable pattern for all enum-returning `.unwrap()` calls
- Affects any `Optional<EnumType>` where the enum has `impl` methods
- Makes test code more verbose

## Workaround

Use an intermediate variable to break the chain:

```simple
val td = result.unwrap()
td.to_text()
```

## Root Cause (Updated)

The bug exists in the **compiled runtime** method dispatch, not the Rust bootstrap interpreter.
The Rust interpreter has been fixed (enum dispatch added to `call_method_on_value` in
`src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`), but the self-hosted
binary uses its own compiled method dispatcher. A re-bootstrap is required to propagate the fix.

**Rust interpreter fix:** Added `Value::Enum` handler for user-defined enums (non-Option/non-Result)
in `call_method_on_value`, mirroring the dispatch logic in `evaluate_method_call`.

## Environment

- Simple compiler: compiled runtime (self-hosted binary)
- Rust bootstrap interpreter: FIXED
- Discovered in: `test/unit/compiler/config/type_inference_config_spec.spl`
- Regression tests: `test/unit/compiler/config/chained_enum_method_spec.spl`
