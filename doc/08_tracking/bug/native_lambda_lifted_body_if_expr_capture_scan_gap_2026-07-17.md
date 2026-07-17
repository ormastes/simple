# Native lambda-value lifting: `if`/`else` anywhere in a lifted lambda body fails loud

**Status:** OPEN
**Discovered:** 2026-07-17, while adding native-seed-parity regression cases for
task T1 (7 recently-fixed native-path bugs). Not a regression from those
fixes — a pre-existing, adjacent gap surfaced while probing their edges.
**Severity:** Medium — silent-safe (loud build/link failure, never a wrong
value), but blocks a common idiom (predicate lambdas with an if/else body)
from being passed as a call argument or to a builtin array method.

## Symptom

A lambda literal that is LIFTED to a standalone function (i.e. passed as a
first-class value: a call argument to an `fn(...)`-typed parameter, or to a
builtin array method like `.filter`/`.map`/`.fold`) fails native-build with a
fatal MIR error if an `if`/`else` expression appears ANYWHERE in its body —
even as the sole tail expression, even with zero free variables:

```simple
fn apply(f: fn(i64) -> bool, x: i64) -> bool:
    return f(x)

fn main() -> i64:
    val r = apply(\v:
        if v > 1:
            true
        else:
            false
    , 5)
    print(r)
    return 0
```

Native-build output:

```
error: MIR lowering error: unsupported MIR expression: HirExprKind::Lambda(...)
```

By contrast, the SAME shape works fine when the lambda is bound to a `val`
and never passed as a value (`val f = \x: if x > 1: true else: false`) —
that path beta-reduces via `try_inline_lambda_call`/`snapshot_lambda_capture`
and never goes through the lift/capture-scan machinery below. It also works
fine when the block body's tail is anything OTHER than an `if` (e.g.
`val doubled = v * 2` / `doubled + 1` lifts and lowers correctly, per
`self_hosted_lambda_block_body_tail_value_2026-07-16.md`).

## Root cause

`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`:

- `lambda_body_captures(body, param_syms)` (~line 1785) and
  `lambda_capture_scan_supported(body)` (~line 1935) are the two functions
  `lower_lambda_value` (~line 2005) consults before lifting a lambda body to a
  standalone function: `if captures and not scan_supported: return nil`.
- Both functions have an explicit `match body.kind:` covering
  `IntLit`/`FloatLit`/`BoolLit`/.../`Binary`/`Unary`/`Field`/`Index`/
  `TupleIndex`/`Cast`/`As`/`Call`/`MethodCall`/`Block`/`Lambda`, with a
  fail-closed `case _:` default (`true` for `lambda_body_captures` = "assume
  it captures", `false` for `lambda_capture_scan_supported` = "cannot scan
  it").
- **Neither function has a case for `HirExprKind::If`.** An if/else
  expression anywhere in the body (as the block tail, or nested inside a
  `Binary`/`Call`/etc. — those recurse into their operands, which can
  themselves be `If`) hits the default arm: `lambda_body_captures` reports
  `true` (captures) and `lambda_capture_scan_supported` reports `false`
  (unsupported) for the exact same node. `true and not false` = `true`, so
  `lower_lambda_value` unconditionally returns `nil` for ANY body containing
  an `If`, regardless of whether it actually references any outer variable.
- The nil then falls through to the ordinary `lower_expr(arg_value)` call-arg
  fallback (`switch_operators_calls.spl` ~line 2324, and the analogous
  `.filter`/`.map`/`.fold` arm in
  `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl` ~line
  2149), which has no case for a bare `Lambda` node at all — producing the
  generic "unsupported MIR expression: HirExprKind::Lambda(...)" fatal error
  (never a silent wrong value; this repo's loud-fail invariant holds).

## Reproductions (verified 2026-07-17 at this worktree's tip)

1. **`fn`-typed call arg**, if/else-only body (`apply(\v: if v>1: true else:
   false, 5)`): native-build fails as above (`unsupported MIR expression`).
2. **`.filter(<lambda>)`**, if/else-only body: fails differently but for the
   SAME root cause —
   `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`'s
   `.filter` arm (~line 2149) calls `lower_lambda_value`, gets `nil`, and
   falls through to the pre-existing "unresolved method call: filter" loud
   error.
3. **Control (isolates the `If` case specifically):** the identical
   `.filter(\x: val doubled = x*2 \n doubled > 2)` — a block body with a
   `val` binding and a NON-`if` tail — lifts and lowers correctly (`kept=3`),
   confirming the gap is specifically `HirExprKind::If`, not block bodies or
   `.filter` lifting in general.
4. **Control (isolates lift-vs-inline):** the identical if/else body as a
   STANDALONE bound lambda (`val f = \x: if x>1: true else: false`, called
   directly, never passed as a value) works via the beta-reduction/inline
   path, confirming the gap is specific to `lower_lambda_value`'s
   capture-scan gate, not `If` lowering in general (if/else lowers correctly
   everywhere else in this compiler).

## Suggested fix

Add an `HirExprKind::If` (three-way: condition, then-block, else-block) case
to both `lambda_body_captures` and `lambda_capture_scan_supported` in
`switch_operators_calls.spl`, mirroring the existing `Block` case's
recursion into a `HirBlock`'s `stmts`/`value` (an if/else arm's `HirBlock` has
the same shape as a lambda block body). `hir_block_stmts_capture` /
`hir_block_stmts_scan_supported` already exist and operate on `[HirStmt]` +
optional tail value — the `If` case for both functions can likely delegate to
those directly for the condition and both arm blocks.

## Do not

- Do not "fix" this by making `.filter`/`.map`/`.fold`/call-arg lambda lifting
  reject if/else bodies more explicitly/quietly — the loud failure is
  already correct; the goal is to make the supported-shape set match what the
  language actually allows (if/else is ordinary control flow, not an exotic
  shape).
- Do not conflate this with the SEPARATE, already-tracked nested-lambda-in-
  lambda-body link failure (`undefined symbol: __lambda_lift_1`, tracked in
  `self_hosted_lambda_block_body_tail_value_2026-07-16.md`'s "Residual gaps"
  section) — reproduced independently in this investigation and still open,
  but a different code path (lift-of-a-lift naming/registration, not the
  capture-scan gate above).
