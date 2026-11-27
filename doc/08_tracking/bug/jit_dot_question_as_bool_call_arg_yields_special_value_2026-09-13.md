# Seed JIT: `.?` passed directly as a `bool` call argument yields a non-boolean special value

## Policy re-check 2026-11-02 (lane a6dffc9c/p12-6)

**Checked against current policy/design: obsolete because it no longer reproduces: `.?` as a `bool` call argument now yields a real boolean on the JIT, matching the interpreter**

Policy: nil only inside `unsafe`, `Option`/`None` elsewhere; no `Any` outside `unsafe`; erased generics (no monomorphization); TDD.

Re-ran the exact repro on the JIT and the interpreter at `2345aff3ff5`:
both print `EQ-true` then `NEQ-true: false` (the report's JIT output was
`NEQ-true: <special:65>` / `NEQ-true: error`). The `if condition:` form is also
correct. Likely fixed by the `.?`-means-presence work (`9a43ca132d0`,
`1df509a0ce5`) and the bool-parameter presence conversion
(`compiler/tests/bool_parameter_presence_jit.rs`); the exact fixing commit was
not bisected. Rows 14 and 15 of `option_payload_pattern_jit.rs` lock
`check(get(true).?)` / `check(get(false).?)` on the JIT. No policy element makes
the old behaviour desirable; closed with evidence, nothing restored.

Evidence (this lane): debug Rust seed built from `2345aff3ff5`
(`cargo build -p simple-driver`, `CARGO_TARGET_DIR=C:/dev/wt/p12-6/target-p12`), JIT
= `simple run`, interpreter = `SIMPLE_EXECUTION_MODE=interpret simple run`.
Regression: `src/compiler_rust/compiler/tests/option_payload_pattern_jit.rs`
(`cargo test -p simple-compiler --test option_payload_pattern_jit`).

- **Date:** 2026-09-13
- **Status:** CLOSED 2026-11-02 - not reproducible at `2345aff3ff5` (fixed since filing)
- **Severity:** P1 — silent wrong branch, and a `<special:65>` value leaking into user-visible output
- **Found by:** July-2026 bug-triage sweep, while re-verifying
  `dot_question_truthy_op_returns_payload_as_call_arg_2026-07-20.md`
- **Lane:** seed JIT only. The tree-walk interpreter
  (`SIMPLE_EXECUTION_MODE=interpreter`) is correct on every case below.

## Symptom

Passing `x.?` directly as an argument to a `bool`-typed parameter produces, on
the seed JIT lane, a value that is neither `true` nor `false`: it compares
unequal to `true` for a present Option, and it is *truthy* for a nil Option —
so an `if condition:` test takes the wrong branch for `nil`.

## Repro (measured 2026-09-13)

```spl
fn check(condition: bool) -> text:
    if condition == true:
        "EQ-true"
    else:
        "NEQ-true: {condition}"

fn get(f: bool) -> text?:
    if f:
        return "payload"
    nil

fn main():
    print(check(get(true).?))
    print(check(get(false).?))
```

| lane | `get(true).?` | `get(false).?` |
|---|---|---|
| tree-walk (`SIMPLE_EXECUTION_MODE=interpreter`) | `EQ-true` | `NEQ-true: false` — correct |
| seed JIT (`run`, the default) | `NEQ-true: <special:65>` | `NEQ-true: error` |

A second form makes the wrong-branch consequence explicit. With a plain
`if condition:` instead of `if condition == true:`, the JIT lane prints
`TRUE-bool` for **both** calls — i.e. `nil.?` is truthy — while the tree-walk
lane correctly prints `TRUE-bool` then `FALSE-bool`.

## Analysis

The JIT lowering of `.?` in argument position does not produce a `bool`. The
interpolated rendering `<special:65>` for the Some case, and `error` for the nil
case, say the argument slot is carrying an internal sentinel rather than a
boolean. Storing the result in an intermediate `val` first is a different code
path and is not affected the same way (`val v = get(true).?` yields the payload
on both lanes, which is the documented Option-valued behaviour of `.?`).

## Relationship to the 2026-07-20 entry

`dot_question_truthy_op_returns_payload_as_call_arg_2026-07-20.md` reported the
*payload* (a struct or a `text`) arriving where a `bool` was expected, under
`bin/simple test`'s SSpec evaluator — i.e. the tree-walk lane. That lane is now
correct (measured, see that entry's closure). This entry records the different,
still-live defect the same re-verification uncovered on the JIT lane.

## Not fixed here

The fix site is in the seed's JIT lowering under `src/compiler_rust/**`. A
bootstrap was running during the triage session that found this, and editing
Rust sources aborts a running bootstrap, so no change was attempted.

## Verification engine

Pinned copy of `src/compiler_rust/target/release/simple.exe`
(Simple Language v1.0.1-beta.1, 39,267,840 bytes, sha256 prefix
`1b62a1a42755774fc087`, built 2026-09-13). Windows 11 / Git Bash.
