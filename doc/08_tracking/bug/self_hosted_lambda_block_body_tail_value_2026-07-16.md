# Self-hosted native-build: block-body lambda never returns its tail value

Date: 2026-07-16
Status: Fixed-pending-land
Severity: High

## Symptom

In native-build, a lambda with a MULTI-STATEMENT (block) body never returns
its tail expression value — every call returns the same constant regardless
of input. Single-expression lambdas (`\x: x > 1`) work fine, and the
identical if/else shape used as a plain `fn` body also works fine. The defect
is specific to block-body `EXPR_LAMBDA` lowering on the native-build path.

Minimal repro (standalone-bound block lambda, no call-arg parsing involved):

```simple
fn main():
    val f = \x:
        val doubled = x * 2
        doubled > 2
    print("f(1)={f(1)} f(2)={f(2)} f(3)={f(3)}")

main()
```

Before the fix: `f(1)=3 f(2)=3 f(3)=3` for every call (a garbage constant,
independent of `x`). Expected: `f(1)=false f(2)=true f(3)=true`.

## Root cause

`src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl` (backslash
lambda case) already parses a block-body lambda correctly: it loops
`parse_statement()` over the indented body and wraps the WHOLE statement list
in a single `EXPR_BLOCK` node (tag 18), then pushes that one node as the
lambda's sole "body" entry: `lam_stmts.push(expr_block(blk_stmts, -1, 0))`.
So `EXPR_LAMBDA`'s stmts slot is always a 1-element list holding either that
`EXPR_BLOCK` node (block body) or a bare expression node (single-expression
body).

`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`'s `EXPR_LAMBDA`
bridge case converted that sole entry with `convert_flat_expr(lambda_body_exprs[0])`
unconditionally. `convert_flat_expr` has **no case for `EXPR_BLOCK`** — the
only code that knows how to unwrap an `EXPR_BLOCK` node into a real `Block`
(list of `Stmt`) is the separate helper `flat_if_branch_block`, used
exclusively by the if-expression bridge. So for a block-body lambda,
`convert_flat_expr` silently fell through its whole if/elif chain to the
generic fallback (`ExprKind.NilLit` / equivalent default), discarding every
statement in the body — including the tail expression — and downstream
HIR/MIR lowering compiled some fallback/garbage constant in its place. This
is why the observed value (`3`) was constant across all inputs: the real
body was never reached at all.

Single-expression lambdas were unaffected because their sole stmts-entry is a
bare expression node (not `EXPR_BLOCK`), which `convert_flat_expr` handles
directly and correctly.

## Fix

`convert_nodes.spl`'s `EXPR_LAMBDA` case now checks the tag of the sole body
entry: if it is `EXPR_BLOCK` (18), it is converted via the existing
`flat_if_branch_block` helper (the same EXPR_BLOCK -> `Block` conversion the
if-expression bridge already uses correctly) and wrapped as
`ExprKind.Block(...)`. HIR's `ExprKind.Block` case already lowers to
`HirExprKind.Block(self.lower_hir_block(block))` — the same tail-value-
extracting block lowering used by if/else branches and match arms — and MIR's
generic expr dispatch already has a working `HirExprKind.Block` case
(`self.lower_block(block)`, used by `try_inline_lambda_call`'s
`self.lower_expr(body)`). No new lowering logic was added in HIR or MIR; the
fix only makes the frontend bridge route block-body lambdas through the
existing, already-correct Block/tail-value machinery instead of silently
dropping them. The bare-expression branch (single-expression lambdas) is
unchanged.

File changed: `src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`
(the `EXPR_LAMBDA` case in `convert_flat_expr`).

## Verification (native-build; native-build interprets `src/compiler/*.spl`
live, no rebuild needed)

- Fresh block-body lambda (comparison tail, no control flow): `f(1)=false
  f(2)=true f(3)=true` — matches hand-computed `doubled=x*2; doubled>2`.
- Plain-tail block lambda (`doubled = x*2` / `doubled + 1`): `f(1)=3 f(2)=5
  f(3)=7` — matches hand-computed.
- If/else-tail block lambda (`if x>1: true else: false`): `f(1)=0 f(2)=1
  f(3)=1` (bool printed as 0/1 on this tail shape — a separate, pre-existing
  display-formatting quirk, not a value defect) — values match hand-computed
  false/true/true.
- Control: single-expression lambda (`xs.filter(\x: x > 1)`), code path
  unchanged by this fix: `kept_len=2` (keeps 2, 3), matches prior
  known-good baseline.
- `sh scripts/check/native-smoke-matrix.shs`: `total=15 pass=15 fail=0
  xfail=0 xpass=0 codegen_fallback_hits=0`.

## Known separate, out-of-scope issue surfaced by this fix

A block-body lambda that both reads AND reassigns an outer `var` inside its
body (`count = count + 1; x + count`, with `count` declared outside the
lambda) now fails MIR lowering loudly (`MIR lowering error: undefined
variable: count`) instead of silently producing a wrong value. Before this
fix such a body was silently dropped entirely, so it "compiled" to a garbage
constant with no visible error. This loud failure is the correct, safe
behavior per this codebase's "never convert a loud failure into a silent
wrong answer" rule, but the underlying capture-mutation gap (the lambda's
by-value capture-snapshot machinery, `snapshot_lambda_capture` /
`try_inline_lambda_call` in `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`,
apparently does not register free variables that are only ever assignment
*targets* inside the body) is a separate, pre-existing bug in the
lambda-capture path, not the tail-value bug this doc tracks. Recommend filing
it separately if/when a real call site needs it.

## Residual loud gaps (2026-07-17, orchestrator verification)

With this fix plus the parser fix landed together, verified at land time:
standalone-bound block lambdas return correct tail values natively
(`f5_combined3`: 2230). Two adjacent shapes remain unsupported and fail LOUD
(never silent): (1) a block lambda inline as a call argument hits
"unsupported MIR expression: HirExprKind::Lambda(..Block..)" in closure
materialization; (2) `.filter(<block lambda>)` reports "unresolved method
call: filter" because the counted-loop filter lowering only matches
expression-bodied lambdas. Plus the capture-mutation gap above. All three are
follow-up work on the MIR lambda path.
