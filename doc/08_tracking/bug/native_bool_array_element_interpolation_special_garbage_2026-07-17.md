# BUG: native backend bool array element via string interpolation prints `<special:N>` garbage

- **Date:** 2026-07-17
- **Status:** source fix implemented; execution pending
- **Area:** compiler native codegen (array element read + bool string interpolation)
- **Severity:** medium (silent wrong output; no crash)

## Symptom

Reading a `bool` value from an array and interpolating it into a string via
`"{x}"` syntax produces garbage output like `<special:N>` instead of the
expected `true` or `false`.

Direct `print x` of the same bool value works correctly (prints `true` or
`false`). The defect is specific to string interpolation of array-read bools.

This affects compiled native-build output; the interpreter does not show
this behavior.

## Minimal repro

```simple
fn main() -> i32:
    var flags: [bool] = [true, false, true]
    var x = flags[0]
    print x                   # Correct: prints "true"
    print "{x}"               # WRONG: prints "<special:0>" or similar garbage
    0
```

Probe: `probe06_debug_bool.spl` (from repro session)

Expected output: `true`
Actual output: `<special:0>` (or `<special:N>` for other indices)

## Impact

Any code using bool arrays and then interpolating element values into text
(logging, error messages, formatted output) will silently produce unreadable
garbage instead of `true`/`false`.

## Workaround

Avoid direct string interpolation of array-read bools:
```simple
var x = flags[0]
var text = if x: "true" else: "false"
print text                    # Correct workaround
```

## Source fix and regression coverage

Two MIR fixes preserve the bool type through the complete failing path:

1. Index lowering retains the array's known element type and applies the
   bootstrap text fallback only when no element type was recovered.
2. Both Let-lowering paths preserve a bool initializer's MIR type when a
   `val` or `var` binding creates a fresh local.

`scripts/check/check-native-seed-parity.shs` adds the strict dual-backend
`bool_array_element_interp` case. It checks direct interpolation of
`flags[0]`/`flags[1]` and interpolation after both `val` and `var` bindings,
with fixed expected `true`/`false` output on LLVM and Cranelift. Executable
verification is pending.

## Cross-reference

Distinct from `native_class_array_field_mutation_segfault_2026-07-17` (that
bug causes crashes on mutation; this causes silent output corruption on read
+ interpolation). Both suggest array-element handling in native codegen has
type/representation issues.
