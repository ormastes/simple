# JIT: `.unwrap_or(default)` on an absent optional returns nil instead of the default

- **Status:** OPEN
- **Severity:** P1 — silent wrong result. No error, no diagnostic, exit 0. The
  caller receives `nil` where it asked for a concrete fallback, so the defect
  propagates into whatever consumes the value.
- **Lane:** Rust seed, **cranelift JIT** (and the default `bin/simple run`
  lane, which is JIT-first). The tree-walk **interpreter is correct**.
- **Class:** cross-engine disagreement on an absent-optional read. Same family
  as `parse_family_strips_option_jit_native_2026-08-02.md`, but a DIFFERENT
  defect — found while verifying that one, not caused by it.

## Reproduction

```
fn none_i() -> i64?:
    nil
fn main():
    print("nil_local_unwrap_or:  " + none_i().unwrap_or(-1).to_string())
    val a = "abc".parse_int()
    print("parse_int_none:       " + a.unwrap_or(-1).to_string())
    val b = "abc".parse_float()
    print("parse_float_none:     " + b.unwrap_or(-1.0).to_string())
    val c: i64? = nil
    print("annotated_nil:        " + c.unwrap_or(-1).to_string())
```

Measured 2026-08-17 against a seed built from the tree at that time:

| check | `SIMPLE_EXECUTION_MODE=interpreter` | `=jit` |
|---|---|---|
| `nil_local_unwrap_or` | `-1` (correct) | **`nil`** |
| `parse_int_none` | `-1` (correct) | **`nil`** |
| `parse_float_none` | `-1.0` (correct) | **`nil`** |
| `annotated_nil` | `-1` (correct) | **`nil`** |

Every form is wrong on the JIT, and every form is right on the interpreter. It
is not specific to a type, to a receiver expression, or to how the optional
became absent.

## Not caused by the parse_int fix landed the same day

This was checked directly rather than assumed, because the two are adjacent.
Running the same program against the PREVIOUS deployed `bin/simple` (built
before the `rt_string_parse_int` change) gives:

```
nil_local_unwrap_or:  nil      <- already wrong
parse_int_none:       0        <- the OLD parse_int defect
parse_float_none:     nil      <- already wrong
annotated_nil:        nil      <- already wrong
```

Three of the four rows are already wrong in the control binary, including both
rows that never touch `parse_int`. So `unwrap_or` was broken independently and
beforehand. The only row the parse fix changed is `parse_int_none`, which moved
from `0` to `nil` — from a value indistinguishable from a *successful* parse of
`"0"` (the silent-wrong-result being fixed) to the same `nil` every other
absent optional already produced. That is forward progress into a
pre-existing defect, not a new regression, and it is why `.is_some()` now
answers correctly where it previously failed to resolve at all.

## Why it stayed hidden

`bin/simple test` runs spec bodies on the tree-walk interpreter, which is
correct here, so no spec can go red on this from an in-process example — the
same structural blind spot recorded in
`run_vs_test_harness_divergence_2026-07-28.md`. Any coverage has to shell out
to a subprocess and pin `SIMPLE_EXECUTION_MODE`.

## Where to look

Not yet root-caused. `unwrap_or` is typed `TypeId::ANY`
(`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs`, the
`"unwrap" | "unwrap_or" | "expect"` arm) and the interpreter handles the
absent case in `Expr::UnwrapOr` (`interpreter/expr.rs`, via
`try_unwrap_option_or_result`). The JIT-side lowering of `UnwrapOr` is the
suspect: the symptom is consistent with the default operand being discarded
and the receiver returned unchanged when the receiver is nil.

Note the runtime primitive it would need is present and correct:
`rt_is_none`/`rt_is_some` (`runtime/src/value/objects.rs:508`) deliberately do
NOT test `value.0 == 0`, so a nil receiver is distinguishable from `Some(0)`.
So this is very likely a lowering gap rather than a runtime one.

## Coverage

Observed by `test/01_unit/compiler/codegen/probe_parse_family_option_jit.spl`
(the `unwrap_or_absent_default` / `nil_unwrap_or_default` checks), which is run
under both engines by
`test/01_unit/compiler/codegen/parse_family_option_preserved_spec.spl`. That
spec asserts this behaviour and is therefore legitimately RED on the JIT arm
until this bug is fixed — per `.claude/rules/testing.md`, a correct spec that
fails is left failing and recorded here rather than weakened.
