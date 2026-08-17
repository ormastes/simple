# Bug: `return` inside a match/if EXPRESSION is swallowed (becomes the expr value)

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

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


## 2026-08-17 CORE-P1 triage: DID NOT REPRODUCE / fix present in current source

Verified against CURRENT SOURCE (content, not SHA ancestry) during the crit_01
CORE-P1 sweep. The triage grep for `ControlFlow::Return` / `Flow::Return` returned zero hits because the enum is actually named `Control::Return(Value)` (`src/compiler_rust/compiler/src/interpreter/core_types.rs:117`). Propagation IS implemented, and not in the `expr/ops.rs` this doc names but in `src/compiler_rust/compiler/src/interpreter/expr/control.rs` -- If at :117, Match arms at :218/:242/:258 and :304, each doing `Control::Return(v) => return Err(CompileError::TryError(Box::new(v)))`, under a comment that names this bug doc by filename: "A `return` inside an if/match EXPRESSION arm must propagate out of the function".
