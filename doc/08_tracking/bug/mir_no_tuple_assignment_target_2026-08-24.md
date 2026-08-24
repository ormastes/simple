# MIR lowering has no assignment-target support for a tuple (2026-08-24)

- **Status:** OPEN — not fixed
- **Severity:** HIGH — blocks `native-build src/app/mcp/main.spl`, and the
  construct is used ~10 times in `src/app/mcp/` alone
- **Area:** `src/compiler/50.mir/mir_lowering_stmts.spl:1740` (pure Simple)
- **Found by:** clearing three earlier blockers in the MCP native-build chain

## Symptom

```
error: in-process native-build: MIR lowering error: unsupported MIR assignment
target: HirExprKind::TupleLit([... NamedVar((SymbolId(id: 429), cwd)),
... NamedVar((SymbolId(id: 430), _rc))])
```

from `src/app/mcp/main_lazy_protocol.spl:63`:

```
fn get_cwd() -> text:
    var cwd = ""
    var _rc: i64 = 0
    (cwd, _rc) = shell_cmd("pwd")
    cwd = cwd.trim()
    cwd
```

This is tuple destructuring as an ASSIGNMENT to already-declared variables. The
DECLARATION forms (`val (a, b) = ...` / `var (a, b) = ...`) are handled: the
parser encodes them as a single `StmtKind.Val`/`Var` whose name is the literal
text `"(a,b)"`, and `lower_hir_stmt_multi`
(`20.hir/hir_lowering/statements.spl:162`) desugars them into N `Let` bindings.
The assignment form has no equivalent path, so it survives into MIR as
`Assign(target: TupleLit([...]), ...)` and falls to the catch-all
`case _: self.error_fatal("unsupported MIR assignment target: ...")`.

## Why this was NOT worked around in the app source

Rewriting `(a, b) = f()` into `val (a, b) = f()` at the call sites is a one-line
change per site, but there are ~10 in `src/app/mcp/` alone
(`main_lazy_protocol.spl:63`, `main_lazy_diag_tools.spl:165,274,281,313,326,422,494,570,580`),
and the repo rule is explicit: when a short, safe form fails, fix it or record a
concrete bug rather than silently normalizing the workaround. Editing ten
application call sites to route around a compiler gap is exactly that
normalization, and it leaves the gap in place for the next caller.

## Shape of the real fix

Desugar at the HIR layer, next to the existing declaration-form desugaring, not
in MIR:

1. In `lower_hir_stmt_multi`, recognise `StmtKind.Assign` whose target is a
   tuple expression.
2. Emit a synthetic `Let` binding the RHS to a fresh temp (evaluating it exactly
   once — the existing `lower_hir_tuple_destructure_val` comment stresses this
   ordering guarantee).
3. Emit N `Assign` statements, each assigning `TupleIndex(temp, i)` to the
   corresponding target.

`HirExprKind.TupleIndex(base, index)` already exists
(`20.hir/hir_definitions.spl:570`) and the MIR expression dispatcher already
carries a `TupleIndex` arm, so step 3 should need no new MIR support.

## NOT verified

- The above is a design sketch, not an implementation. It was not written and
  not tested.
- Whether `lower_hir_tuple_destructure_val`'s restriction to LITERAL tuple
  initializers (it raises a loud HIR error for a call initializer) also applies
  to the assignment form's RHS was not determined. If it does, the fix is
  larger than the sketch: `shell_cmd("pwd")` is a call, not a literal.
