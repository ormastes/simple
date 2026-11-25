# Bug (or undocumented semantics): `fn f(x: mut i64)` mutating `x` does not propagate back to the caller's variable

## Triage 2026-11-25 (lane p2w3-aa) — still reproduces on the seed; semantics decision now partially documented

Reproduced on the tracked Windows seed (`bin/simple.exe`, Rust seed
v1.0.0-rc.1) with the doc's minimal repro via `SIMPLE_LIB=src bin/simple.exe
run`: prints `n = 41` (caller's `var n` unchanged), identical to the original
2026-07-20 filing. The spec assertion (`expect n == 42`,
`test/feature/usage/parser_type_annotations_spec.spl:259`) is unchanged.

Since the filing, `doc/07_guide/quick_reference/syntax_quick_reference.md`
("Ownership Capabilities (`iso`/`mut`)") now documents that `mut T` parses in
parameter position but is **not enforced through `bin/simple`** (the seed has
no borrow-check code; enforcement belongs to the self-hosted compiler, and
stage-3 self-host is blocked). That answers the "undocumented semantics"
half: today `mut T` parameters are local-only on every runnable engine.
Whether `mut T` should *eventually* mean caller-visible by-reference mutation
for primitives remains an owner/language-design decision, and any
implementation lives in the Rust seed (out of scope for a pure-Simple bug
lane) or the blocked self-hosted borrow checker. Left OPEN pending that
decision; no code change. End-to-end spec run additionally blocked at HEAD by
the known `unknown decorator '@representation_boundary'` source/binary
inconsistency.

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
