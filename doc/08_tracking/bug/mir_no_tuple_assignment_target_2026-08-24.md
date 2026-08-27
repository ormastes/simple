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

## 2026-08-24 (later) — FIXED, and the sketch above was wrong about WHERE

**Status: FIXED** by `lower_hir_tuple_destructure_assign` in
`20.hir/hir_lowering/statements.spl`.

The design sketch's step 1 named the wrong hook. `lower_hir_stmt_multi` is not
on this statement's path, and neither is either of the two
`StmtKind.Assign` arms in `lower_hir_stmt`. Both were tried and BOTH were dead
for this input — a probe placed in the fast-path Assign branch never printed.
**The flat parser emits every `target = value` as an EXPRESSION statement**
(`ExprKind.Assign` inside `StmtKind.Expr`), which the file already documents at
the `case ExprKind.Assign(...)` arm: *"The flat parser emits `target = value` as
an EXPRESSION statement (expr_assign), never StmtKind.Assign."* That arm is the
only working hook, and it is where the desugar now lives.

The other two `StmtKind.Assign` paths are deliberately NOT patched. No input in
this lane reached them, so hooking them would be untested code; a tuple target
arriving there still produces the loud MIR error, which is a clear diagnostic
rather than a silent wrong answer.

Steps 2 and 3 of the sketch were right, and the open question it flagged
resolved favourably: the declaration form's literal-tuple-only restriction does
NOT apply, because `lower_hir_tuple_destructure_val`'s own `case _` arm already
routes non-literal initializers (including calls) to the general
`lower_tuple_destructure`. The new method mirrors that general path: bind the
RHS to one temp so a call is evaluated exactly once, then read element `i` via
`Index(temp, i)`, assigning to the existing place instead of defining a symbol.

Element TYPES are recovered from the same by-NAME `fn_tuple_returns` registry
the declaration path uses. This is load-bearing, not decoration: with a nil
element type the locals default to i64 and a `text` element's handle renders as
a decimal integer. The fixture below pins it — `len=5` on the destructured text
would be impossible if the element had decayed to a handle.

A bare `_` target discards its element, matching the `pname != "_"` skip in
`lower_tuple_destructure`. `_rc` / `_unused` are ordinary names and are assigned
normally.

### Verified (clean worktree, fresh seed, fresh SIMPLE_CACHE_SCOPE)

```
pub fn pair() -> (text, i64): ("hello", 7)
...
var s = ""
var n: i64 = 0
(s, n) = pair()
print("s={s} n={n} len={s.len()}")
```
builds, links, runs -> `s=hello n=7 len=5`.

Three-element with a hole, assigned twice:
```
(x, _, z) = triple()
(x, k, z) = triple()
```
-> `x=a z=c k=3 zlen=1`.

The match-arm fixture from the sibling records still builds and runs (`v=10`),
so nothing regressed.

### Effect on the MCP build, and the next blocker

`native-build src/app/mcp/main.spl` now clears MIR lowering for all 61 modules
and stops on a FIFTH, unrelated defect — a known, numbered feature gap rather
than a bug:

```
error: MIR lowering error: for-in over non-array iterables is not supported by
native codegen yet (#143); iterate an array or use while
```

That is a deliberate unimplemented-feature diagnostic in native codegen, not a
regression, and it is out of scope here.
