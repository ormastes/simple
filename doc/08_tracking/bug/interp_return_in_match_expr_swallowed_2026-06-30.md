# Bug: `return` inside a match/if EXPRESSION is swallowed (becomes the expr value)

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
