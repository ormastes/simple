# No call-site argument checking on the HIR / native compile path (arity AND type)

- **Filed:** 2026-08-24 (Lane P, slice A: `00.common`, `10.frontend`, `15.blocks`, `20.hir`)
- **Status:** OPEN — detection venue identified, fix NOT attempted (see "Why not fixed here")
- **Severity:** high — silently accepts ill-typed and wrong-arity calls; the whole
  "bool literal reaching an enum parameter" defect class descends from this.

## Summary

`simple compile <file> --format=smf` performs **no argument checking at all** at
call sites. Neither the number of arguments nor their types is compared against
the callee's declared signature. Both fixtures below reach
`point=post-diagnostics count=0` — a clean bill of health.

## Reproduce (both fail today: they should error, they report 0 errors)

Compiler under test:
`build/bootstrap/goal-r3/stage2/x86_64-unknown-linux-gnu/simple`
(132945096 bytes, 2026-08-24 02:50)

### Fixture 1 — bool literal passed to an enum parameter
`test/01_unit/compiler/30.types/fixtures/call_arg_bool_to_enum.spl`

```
enum Vis:
    Public
    Private

fn take(v: Vis) -> i64:
    match v:
        case Vis.Public: 1
        case Vis.Private: 2

fn main():
    print(take(false))
```

Observed:
```
[bootstrap-error-count] source_idx=0 point=post-lowering count=0
[bootstrap-error-count] source_idx=0 point=post-diagnostics count=0
```
Expected: a type error naming parameter `v` (`Vis`) and the supplied `bool`.

### Fixture 2 — wrong arity
`test/01_unit/compiler/30.types/fixtures/call_arg_arity.spl`

```
fn take(a: i64, b: i64) -> i64:
    a + b

fn main():
    print(take(1))
```

Observed: identical — `post-diagnostics count=0`.
Expected: `expected 2 argument(s), found 1`.

## Root cause

Two independent pieces of evidence:

1. **The diagnostics exist but are dead code.**
   `src/compiler/00.common/error.spl:337` `argument_type_mismatch(index, expected, found)`
   and `:342` `argument_count_mismatch(expected, found)` have **zero call sites**
   anywhere under `src/` (`/usr/bin/grep -rn 'argument_type_mismatch\|argument_count_mismatch' src/`
   returns only the two definitions). The error vocabulary was written; the check
   that would raise it never was.

2. **The signature is not in scope where the call is built.**
   HIR lowering constructs calls at
   `src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl:89`:
   ```
   HirExpr(kind: HirExprKind.Call(self.lower_hir_expr(call_callee_t), hir_args, []), type_: nil, span: e.span)
   ```
   The callee is an untyped `HirExpr` (`type_: nil`) and method calls carry
   `MethodResolution.Unresolved` (`:175`, `:557`). No resolved callee signature is
   available at construction time, so nothing at this point *can* compare
   arguments to parameters.

**The interpreter path does check** — `src/compiler/10.frontend/core/interpreter/eval_calls.spl:227`
and `_EvalOps/call_method_eval.spl:332` both emit
`type error: argument '<param>' in function '<fn>' type mismatch`. So the gap is
specific to the HIR/native compile path, which is exactly the path the bootstrap
and every shipped binary take. Code that runs clean under `simple run` can be
ill-typed and still compile.

## Where detection belongs

Per the standing principle ("if lint can detect the bug update lint; if it is
easy/fast detectable place it on the compiler"):

- **Compiler — correct venue, but not a one-line fix.** The check belongs after
  callee resolution (`src/compiler/35.semantics/resolve*.spl`, which already
  reads `params.len()` at `resolve_lookup_helpers.spl:129,133` and
  `resolve_strategies.spl:273`), raising through the already-written
  `argument_count_mismatch` / `argument_type_mismatch` helpers. That revives dead
  code rather than adding new surface.
- **Lint — cannot cover the motivating case.** `src/compiler/35.semantics/lint/argument_count.spl`
  exists but checks *declaration* parameter counts (ARG001/ARG002), not call
  sites, and works on the file-local arena AST. The motivating defect,
  `self.symbols.define(...)`, is a method call across modules; a file-local lint
  rule cannot resolve the callee, so a lint rule here would be both new surface
  and blind to the real case. Rejected.
- **`scripts/check/` gate — rejected.** Argument/parameter agreement is a type
  property, not a structural invariant; a text gate would be unreliable.

## Why not fixed here

Turning the check on is not a local edit: it needs the resolved callee signature
plumbed to the call site and will surface findings across the whole tree, with a
real risk to the bootstrap. Under "preserve architecture, fix bugs only" and
"never over-engineer" that is a separate, scoped change with its own bootstrap
verification, not a side effect of a compile census. Filed with reproduce
fixtures so the fix lands against a failing test.

## Note on the briefed premise

Lane P was briefed that 25 `SymbolTable.define()` call sites pass the bool
literal `false` in the `visibility: Visibility` slot
(`src/compiler/20.hir/hir_types.spl:316`). **That is no longer true in this
tree.** All 55 `.define(...)` call sites under `src/compiler` pass 7 arguments
with a `Visibility`-typed expression in position 5 (`Visibility.Public`,
`decl_visibility` — itself `val decl_visibility = Visibility.Public` at
`module_declarations_bootstrap.spl:47` — `fn_.visibility`, `method.visibility`,
`fld.visibility`). Zero sites pass `true`/`false` there. The call sites were
fixed; the type hole that let them through was not, and this record is that hole.
