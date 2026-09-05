# `val x = s.slice(0, 2).len()` fails with E3009 while the same chain inline succeeds

Status: OPEN
Found: 2026-08-21, while writing regression tests for
`doc/08_tracking/bug/native_slice_splits_utf8_three_divergent_policies_2026-08-01.md`.

## Summary

In the interpreter, binding a two-link method chain on a `text` receiver to a
`val` is rejected, while the byte-identical expression used inline in a
condition evaluates fine. The failure is in the BINDING, not in either method.

```
fn main() -> i64:
    val s = "a\u{E9}\u{20AC}\u{1D11E}z"
    val a = s.slice(0, 2).len()      # E3009 -- rejected
    if s.slice(0, 2).len() == 2:     # same expression, accepted
        return 0
    1
```

Error text, verbatim:

```
method 'len' not found on value of type str in nested call context
code: E3009
help: check that the method is defined on this type
```

## Why it matters

This is the "short, safe form fails and forces a workaround" case the repo's
rules name explicitly. The workaround (inline the chain, or split it across two
`val`s) is silent and looks like a style choice in the source, so the gap is
invisible to a later reader and gets copied forward.

## Where it was worked around

`src/compiler_rust/compiler/tests/interpreter_utf8_slice_boundary.rs` writes
every chain inline and carries a NOTE pointing at this record. Removing that
NOTE without fixing the gap would erase the only marker that the spelling was
forced.

## Reproduce

Run the snippet above through the interpreter
(`SIMPLE_EXECUTION_MODE=interpret`, or `interpreter::evaluate_module`).
Not measured on the JIT/native lanes.

## Not investigated

The receiver type is reported as `str`, and the message says "in nested call
context", which suggests the method-resolution path used when a call is the
initializer of a binding differs from the one used inside a condition. The
site was not located; that is the first step for whoever picks this up.
