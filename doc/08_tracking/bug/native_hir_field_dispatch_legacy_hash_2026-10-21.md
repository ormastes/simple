# Native HIR field dispatch compares an obsolete enum hash

Date: 2026-10-21
Status: source fix authored; native verification pending.

## Failure and evidence

The native HIR ownership diagnostic, `build/nogc-hardening/nogc_hir_contract_probe_v8`,
built successfully but stopped at its prerequisite guard:
`source fixture produced HIR lowering errors`.

Read-only GDB diagnosis identified the second `report` fixture, with strict mode
disabled:

```simple
fn forward(n: Node) -> i64:
    later(n)
fn later(n: Node) -> i64:
    n.v
```

`HirLowering.error` received `unsupported expression kind`. Its stack came from
`expression_core.lower_hir_expr`, through statement/block/function lowering,
into the fixture's `report` helper. The saved AST expression's enum object had
discriminant **11**, the current `ExprKind.Field` tag. The Field predispatch at
`src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl` instead
compared with **21232742**, a legacy seed variant-name hash. Field deliberately
has no ordinary match arm because this predispatch avoids a historical
struct/enum pattern-name collision. Missing the predispatch therefore reached
the unsupported-expression diagnostic.

The local diagnostic command script is
`build/nogc-hardening/hir-v8-lowering-error.gdb`. It records each report source,
breaks at the actual lowering error, and inspects the saved enum object. GDB
execution was diagnostic evidence, not an acceptance-test pass.

## Source repair

Derive the Field comparison from
`hir_expr_kind_disc(ExprKind.Field(kind_disc_dummy, ""))`, matching the adjacent
constructor-derived dispatches. This follows the active producer's enum
representation without accepting a second guessed tag or suppressing errors.
The adjacent Block predispatch now likewise derives its tag from
`ExprKind.Block(Block(stmts: [], span: e.span))`, using the same concrete Block
construction already used by neighboring dispatch checks.

The existing `nogc_hir_contract_probe.spl` forward-call fixture is the regression
case. Its parser/nonempty-function and lowering-error guards remain mandatory;
new error/source printing exposes any subsequent prerequisite failure.

## Adjacent issue and verification limits

The separate Block predispatch formerly compared with **1138084884**. Its
repair addresses the analogous source hazard; GDB directly established only
the Field failure. No native build or test was run for either source fix by
its author. The v8 binary predates both fixes and must not qualify them.
