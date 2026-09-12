# Bug: `return` inside a match/if EXPRESSION is swallowed (becomes the expr value)

**Status:** OPEN (confirmed still reproduces 2026-09-12)

**Status:** CLOSED (2026-09-12) — not reproducible; see "Re-check 2026-09-12" at the end.
**Date:** 2026-06-30
**Severity:** High — a whole CLASS of `Result`-handling failures. Any
`val x = match r: case Ok(v): v; case Err(e): return Err(e)` leaves `x` bound to
the Err enum and crashes downstream ("cannot convert enum to int", "method len
not found on type enum", "tuple index access on non-tuple type enum").
**Component:** Rust seed interpreter — expression-level control flow
(`interpreter/expr/control.rs`, `interpreter/expr.rs::evaluate_expr`).

## Minimal reproducer

```simple
fn f(r: Result<i64, text>) -> Result<i64, text>:
    val x = match r:
        case Ok(v): v
        case Err(e): return Err(e)   # should return from f; instead x = Err(e)
    Ok(x + 1)
fn main():
    val b = f(Err("bad"))            # error: cannot convert enum to int
```

## Root cause

`return` parses to `Node::Return` → `exec_node` → `Control::Return(value)`
(node_exec.rs:260). That works at the STATEMENT level (exec_block catches
Control::Return and returns from the function). But when the `return` is the body
of a **match/if EXPRESSION arm**, the match is evaluated by `eval_control_expr`
(an EXPRESSION evaluator whose signature is `Result<Value, CompileError>` — it
cannot carry a `Control` signal). On `Control::Return(v)` it does
`return Ok(Some(v))` (control.rs:185/204/215) — which makes the **match
expression evaluate to `v`**, i.e. the function-return is converted into the
expression's value and silently swallowed. The same applies to `if`-expressions
used as values with a `return` arm.

There is currently NO mechanism to propagate a function-return out of an
expression: no `CompileError::EarlyReturn`, no pending-return thread-local.

## Proper fix (deliberate — high blast radius, NOT a rush job)

Add a control-flow-carrying error variant, e.g. `CompileError::EarlyReturn(Value)`:
- `eval_control_expr` (and any expr path that evaluates statement bodies) returns
  `Err(EarlyReturn(v))` instead of `Ok(Some(v))` for `Control::Return(v)`.
- It propagates via `?` up to the function boundary
  (`interpreter_call/core/function_exec.rs`), which catches `EarlyReturn` and
  returns the value (mirroring how `exec_block` catches `Control::Return`).
- Audit every site that does `match evaluate_expr(...) { Err(e) => ... }` (rather
  than `?`) so the new variant isn't mis-handled — especially the test runner's
  `catch_unwind` and any error-classification code.
Touches core control flow; needs a full bootstrap + regression pass.

## Workaround (LANDED at call sites)

Avoid `match`-with-`return`; branch explicitly:
```simple
if not r.is_ok():
    return Err(r.unwrap_err())
val x = r.unwrap()
```
Applied to `encoding/base58.spl` and `hpack/decoder.spl` (§6.1 + _decode_string).
The same pattern appears ~238 times across `compress/*` and elsewhere — most work
(only the Err-arm-taken paths crash), so a blanket rewrite is unwarranted; the
seed fix is the real solution.

## Re-probed 2026-09-06 — NOT REPRODUCIBLE

Binary probed: `bin/release/aarch64-unknown-linux-gnu/simple` (Rust seed,
aarch64). Both engines exercised: `SIMPLE_EXECUTION_MODE=interpret` (tree-walk)
and `env -u SIMPLE_EXECUTION_MODE` (default Cranelift JIT). Probe sources are
listed with each entry; they were run on both lanes and compared.

The record's exact minimal reproducer now returns correctly from `f` on both
lanes:

```
ERR_OK=bad     OK_OK=42      # interpret
ERR_OK=bad     OK_OK=42      # jit
```

(`f(Err("bad"))` propagates the Err instead of binding `x` to it, and
`f(Ok(41))` returns `Ok(42)`.) Probe `_scratch/retmatch.spl`.

The "proper fix" this record specified — a control-flow-carrying error variant
propagated to the function boundary — IS implemented, under a different name
than the proposed `CompileError::EarlyReturn`: `interpreter/expr/control.rs`
now does `Control::Return(v) => return Err(CompileError::TryError(Box::new(v)))`
at five sites (`:167`, `:280`, `:304`, `:320`, `:362`). Grepping for
`EarlyReturn` finds nothing, which is why this can look unfixed. Not fixed by
this session.

## Triage 2026-09-12
Re-verified 2026-09-12: ran the record's own minimal repro (`return` inside a `match` expression assigned to `val x`); it still misbehaves — printed a raw `<enum@0x...>` pointer instead of a clean result, confirming `return` inside a match/if expression is still swallowed. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

## Re-check 2026-09-12

Binary: `bin/simple` = Rust seed `bin/release/aarch64-unknown-linux-gnu/simple`,
sha256 `3d120a6f9ab5704b…`, `Simple Language v1.0.0-rc.1` (aarch64 host).

The record's own minimal reproducer:

```
$ SIMPLE_EXECUTION_MODE=jit         bin/simple run m.spl
good=Ok(42) bad=Err(bad)
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run m.spl
good=Ok(42) bad=Err(bad)
```

`f(Err("bad"))` returns `Err("bad")` rather than binding the `Err` to `x` and
falling into the tail expression, and it does not raise "cannot convert enum to
int". **Not reproducible** — status CLOSED.

Regression guard: `test/01_unit/bugs/interp_return_in_match_expression_spec.spl`
(6 examples). Two things about how it is written matter:

- The load-bearing examples are on the **Err** path. The `Ok` path never
  exercised the defect, so an `Ok`-only guard would be vacuous; the `Ok`
  examples are kept only so a future failure is attributable to the early
  return rather than to `match` itself.
- The assertions are on the function's **return value**, not on the absence of
  a downstream crash. "It did not crash" is not evidence the early return
  happened — the swallowed form could equally have produced a plausible value.
  A second helper (`side_effect_count`) separately proves the tail expression
  was not reached, by returning a sentinel from the arm.

```
SPEC FILE VERDICT: test/01_unit/bugs/interp_return_in_match_expression_spec.spl outcome=OK declared>=6 executed=6 passed=6 failed=0 skipped=0 dropped=0
```

Non-vacuity proof: substituting the results the swallowed-return form would
produce turns the file RED —
`outcome=ERROR declared>=6 executed=6 passed=4 failed=2 skipped=0 dropped=0`.
