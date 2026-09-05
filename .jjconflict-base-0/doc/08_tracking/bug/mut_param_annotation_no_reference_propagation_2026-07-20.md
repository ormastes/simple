# Bug (or undocumented semantics): `fn f(x: mut i64)` mutating `x` does not propagate back to the caller's variable

- **Date:** 2026-07-20
- **Status:** open (found triaging `test/feature/usage/parser_type_annotations_spec.spl`)
- **Area:** `mut T` parameter annotation semantics (interpreter — pass-by-value
  vs pass-by-reference for primitives), deployed seed at
  `bin/release/x86_64-unknown-linux-gnu/simple`

## Symptom

```
✗ parses mutable reference
  fn modify(x: mut i64):
      x = x + 1
  var n = 41
  modify(n)
  expect n == 42          --> expected 41 to equal 42
```

`n` is unchanged after `modify(n)` — the reassignment of the `mut i64`
parameter inside `modify` does not propagate back to the caller's `var n`.

## Caveat — genuine bug vs. undocumented/misunderstood semantics

No independent documentation of `mut T` parameter semantics was found in
`doc/07_guide/quick_reference/syntax_quick_reference.md` (no hits for `mut
i64`, "mutable reference", or "by reference" in that file) to confirm whether
`mut T` parameters are *intended* to be by-reference for primitive types. The
spec file's own section is titled "Test Group 8: Reference Type Annotations"
and its stated purpose is narrower than the assertion tests
("Tests parsing of reference type annotations" — i.e. the file's own remit is
PARSING correctness, not necessarily full runtime by-reference semantics),
which raises the possibility that this specific runtime assertion
(`expect n == 42`) was written on an assumption not otherwise confirmed
elsewhere in the codebase. Filing as a bug rather than silently rewriting the
assertion, since "the parameter reassignment inside the function is invisible
to the caller" is worth an explicit decision either way (implement
by-reference primitive mutation, or fix the spec + document that `mut T`
params are local-only).

## Minimal repro

```simple
fn modify(x: mut i64):
    x = x + 1

fn main():
    var n = 41
    modify(n)
    print("n = " + n.to_text())
```

## Verification

Reproduced at repo tip (2026-07-20) via:
```
bin/release/x86_64-unknown-linux-gnu/simple test test/feature/usage/parser_type_annotations_spec.spl --no-session-daemon
```
Not checked against the pure-Simple self-hosted compiler or a compiled/native
path — only the Rust seed interpreter was probed.
