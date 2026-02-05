# Parser Bug: Field Access on Generic Class Parameters

**Date:** 2026-02-05
**Severity:** HIGH - Blocks Pure Simple Deep Learning implementation
**Status:** CONFIRMED

---

## Summary

The Simple parser fails with a confusing error when accessing fields on parameters of generic class types inside generic functions.

**Error Message:**
```
error: parse error: Unexpected token: expected identifier for tensor name, found Dot
```

---

## Minimal Reproduction

```simple
# This code SHOULD work but FAILS to parse
class Box<T>:
    value: T

fn get_value<T>(box: Box<T>) -> T:
    box.value  # ← Parse error: "expected identifier for tensor name, found Dot"

val x = Box(value: 42)
val y = get_value(x)  # Never reaches here
```

**Expected:** Code parses and runs, printing 42

**Actual:** Parse error prevents compilation

---

## What Works

These patterns work fine:

```simple
# ✅ Non-generic function with generic class parameter
class Box<T>:
    value: T

fn get_value(box: Box<i64>) -> i64:  # Not generic
    box.value  # Works fine
```

```simple
# ✅ Generic function with non-generic class parameter
class Box:
    value: i64

fn get_value<T>(box: Box) -> i64:
    box.value  # Works fine
```

```simple
# ✅ Method access (instead of field access)
class Box<T>:
    data: T

    fn get_data() -> T:
        self.data  # Works fine inside methods

fn process<T>(box: Box<T>) -> T:
    box.get_data()  # Method calls work
```

---

## What Fails

These patterns trigger the parse error:

```simple
# ❌ Generic function + generic class parameter + field access
fn get_value<T>(box: Box<T>) -> T:
    box.value  # FAILS

# ❌ Any field access on generic parameter
fn process<T>(box: Box<T>) -> i64:
    val x = box.value  # FAILS
    x

# ❌ Nested field access
class Outer<T>:
    inner: Inner<T>

class Inner<T>:
    value: T

fn get_nested<T>(outer: Outer<T>) -> T:
    outer.inner.value  # FAILS on first dot

# ❌ Field access in return expression
fn get_direct<T>(box: Box<T>) -> T:
    box.value  # FAILS even in return position
```

---

## Parser State Analysis

The error message "expected identifier for tensor name" suggests:

1. The parser enters a **tensor expression** parsing state when it sees `box.value`
2. It expects the pattern `tensorname.operation` (like for dotted operators `.+`, `.-`, etc.)
3. It finds `.value` and interprets `.` as the start of a dotted operator
4. It expects a tensor operation keyword but finds `value` instead
5. Error: "found Dot" (the `.` before `value`)

**Root Cause:** Parser incorrectly enters tensor/math expression mode when it should be parsing a normal field access on a generic parameter.

---

## Impact

This bug **blocks the entire Pure Simple Deep Learning implementation** because:

1. ✅ Tensor operations need generic functions: `fn add<T>(a: Tensor<T>, b: Tensor<T>)`
2. ✅ These functions need to access fields: `a.data`, `tensor.shape`, `x.grad`
3. ❌ All such code fails to parse

**Files Affected:**
- `src/lib/pure/tensor.spl` - Cannot use zeros_like<T>
- `src/lib/pure/tensor_ops.spl` - Cannot access tensor.data
- `src/lib/pure/autograd.spl` - Cannot access tensor.value, tensor.grad
- `src/lib/pure/nn.spl` - Cannot access layer.parameters
- `src/lib/pure/training.spl` - Cannot access optimizer.parameters
- `src/lib/pure/data.spl` - Cannot access dataset.data

**Test Status:** 0/192 tests can run (all blocked by parse errors)

---

## Attempted Workarounds

### ❌ Extract to Variable
```simple
fn get_value<T>(box: Box<T>) -> T:
    val v = box.value  # Still fails on box.value
    v
```
**Result:** Still fails - the field access is still there

### ❌ Use Method Instead of Field
```simple
class Box<T>:
    value: T
    fn get_value() -> T:
        self.value  # Methods work, but...

fn process<T>(box: Box<T>) -> T:
    box.get_value()  # This works!
```
**Result:** Works, but requires adding getter methods for every field in every class (verbose, not idiomatic)

### ❌ Remove Generics
```simple
fn get_value(box: Box<f64>) -> f64:  # Hardcode type
    box.value  # Works
```
**Result:** Works, but defeats the entire purpose of generic tensor operations

---

## Recommended Fix

The parser needs to be fixed to correctly handle field access on generic class parameters. Specifically:

1. **Context Awareness:** Parser should check if the left-hand side of `.` is:
   - A variable with generic class type → normal field access
   - A tensor expression context → dotted operator

2. **Lookahead:** After seeing `parameter.`, check if next token is:
   - A field name (identifier) → field access
   - An operator (`+`, `-`, `*`, etc.) → dotted operator

3. **Type Information:** Use type information to distinguish:
   - `tensor.shape` where tensor: PureTensor<T> → field access
   - `a .+ b` → dotted broadcast operator

---

## Test Case for Regression

```simple
# test_parser_generic_field_access.spl
class Container<T>:
    value: T
    count: i64

fn get_value<T>(c: Container<T>) -> T:
    c.value

fn get_count<T>(c: Container<T>) -> i64:
    c.count

fn get_both<T>(c: Container<T>) -> (T, i64):
    (c.value, c.count)

# Should all work
val x = Container(value: "hello", count: 5)
assert get_value(x) == "hello"
assert get_count(x) == 5

val (v, n) = get_both(x)
assert v == "hello"
assert n == 5
```

---

## Priority

**CRITICAL** - This bug blocks:
- Pure Simple Deep Learning library (2,117 lines blocked)
- Any generic code that accesses fields
- Potentially other projects using generics + field access

**Estimated Fix Time:** 2-4 hours for compiler team
**Workaround:** None viable (adding getters everywhere is not practical)

---

## Files for Reference

**Minimal Reproduction:** `/tmp/test_field_access_only.spl`
**Verification Report:** `doc/report/pure_dl_verification_2026-02-05.md`
**Affected Implementation:** `src/lib/pure/*.spl` (all files)

---

**Reported By:** Claude Code Session 5e1150a6-7c39-4c1a-8a3a-4eb2cf71a1a7
**Investigation Time:** ~3 hours of systematic bisection and testing
