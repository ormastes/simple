# Seed JIT: `any + any` on floats adds shifted heap pointers (2026-11-12)

Status: FIXED in the same change (Rust runtime `rt_any_add`).

## Repro

```simple
fn anyf(x: i64) -> any:
    x * 1.25

fn main():
    val p = anyf(2)
    val q = anyf(4)
    print "add={p + q} mul={p * q}"    # expect add=7.5 mul=12.5
```

Seed JIT (no fallback, no error): `add=657650110958 mul=12.5`. The same
happens for an erased generic result (`pick(2.5, 0.0) + pick(2.0, 0.0)`) and
for a mixed `float + int`.

## Cause

`any + any` lowers to `rt_any_add`. The Rust runtime's `rt_any_add`
(`src/compiler_rust/runtime/src/value/collections.rs`) had a string lane and
an integer lane only, so two tagged floats went through `as_int()`.
`rt_any_sub` / `rt_any_mul` / `rt_any_div` / `rt_any_mod` already promote
through `any_binop_is_float`; `add` was the odd one out.

## Fix

Float lane added to `rt_any_add`, identical to the other operators.
Test: `any_add_promotes_float_operands_like_the_other_any_operators`
(`runtime/src/value/tagged_add_tests.rs`), red before, green after.

## Not changed

`src/runtime/runtime_native.c` `rt_any_add` is the legacy raw-word ABI
(`left + right`) of a different lane and is left as is.
