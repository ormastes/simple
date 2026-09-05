# Async desugar destructured `ExprKind.Binary` payloads in the wrong order

- **Filed:** 2026-08-21
- **Status:** FIXED
- **Severity:** blocker — killed every self-hosted `native-build` whose closure
  contained an `async fn` with a binary expression
- **Area:** `src/compiler/10.frontend/desugar/`

## Symptom

A self-hosted `native-build` of the lint entry closure (192 modules) aborted at
the end of step 1/6 with a single, location-less error:

```
error: semantic: undefined field: unknown property or method 'kind' on enum BinOp
!!!!!! END NATIVE-BUILD TRUNCATED STDERR !!!!!!
error: native-build worker exited with code 1.
```

The error is emitted mid-log while parse progress lines keep scrolling, so it
*looks* non-fatal; it is not. The worker exits 1 and no later phase (HIR
lowering, mono, codegen, link) is ever reached.

## Root cause

`ExprKind.Binary` is declared operator-first
(`src/compiler/10.frontend/parser_types_expr.spl:349`):

```
Binary(BinOp, Expr, Expr)
```

Both async-desugar analyzers destructured it operand-first:

| file | line(s) | pattern |
|---|---|---|
| `desugar/suspension_analysis.spl` | 229, 343, 470 | `case ExprKind.Binary(left, op, right):` |
| `desugar/spawn_analysis.spl` | 286, 478 | `case ExprKind.Binary(left, _, right):` |

So `left` bound the **BinOp**, and `op` bound the real left operand. In
`suspension_analysis` the next statement is `self.visit_expr(left)`, which calls
`expr_kind(expr)` → `expr.kind`. `kind` is a field of `struct Expr`, not of
`enum BinOp`, hence the message. The correct sites elsewhere in the tree
(`20.hir/.../module_callable_types.spl:285`, `expression_core.spl:458`, and the
constructor in `_FlatAstBridge/convert_nodes.spl:871`) all use operator-first
order, confirming the declaration is right and these two files were wrong.

`spawn_analysis` had the same swap but did **not** crash — it silently analyzed
the wrong nodes (operator slot treated as left operand, left operand as right),
dropping real callees and spawn sites. A correctness bug masked by the absence
of a crash.

## How it was located

The error carried no file/line. The seed already had a gated field-access trace
(`SIMPLE_DEBUG_FIELD_ACCESS=1` / `SIMPLE_BOOTSTRAP_DIAG=1`) but it was wired
only to the *non-enum* arm of the field-access error path, so an enum receiver
printed nothing. Adding the same gated `eprintln!` to the enum arm
(`src/compiler_rust/compiler/src/interpreter/expr/calls.rs`, default-off,
no behaviour change) immediately produced:

```
[field-access-error] field=kind recv_type=enum BinOp recv=BinOp::Lt
  expr=Identifier("expr")
  stack=parse_full_frontend -> desugar_module -> desugar_async_function
     -> analyze_suspensions -> visit_block -> visit_stmt -> visit_expr -> expr_kind
```

That diagnostic is kept — it is the reason this took minutes instead of a
bisect, and the next location-less field error will need it too.

## Fix

Reorder the five patterns to match the declaration:

- `suspension_analysis.spl` → `case ExprKind.Binary(op, left, right):`
- `spawn_analysis.spl` → `case ExprKind.Binary(_, left, right):`

## Reproduce spec

`test/01_unit/compiler/frontend/async_binary_operand_order_spec.spl` — three
cases driving `parse_full_frontend`: an `async fn` with `a < b`, an `async fn`
with binary arithmetic, and a **sync** positive control with the same `a < b`
body. The two async cases fail pre-fix with the exact error above; the sync
control passes both pre- and post-fix, pinning the failure to the async
desugar path rather than to binary parsing generally.
