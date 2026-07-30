# Two bare `_` placeholders in one string template: `variable __p1 not found`

- **Filed:** 2026-07-30
- **Severity:** medium — silently unusable feature shape (string template with
  a repeated bare placeholder), no known workaround inside the template
  itself
- **Status:** open — root cause NOT pinned down; mechanism confirmed distinct
  from the nested-call-arg bug fixed alongside it
- **Found via:** lane TMF1 (mission-critical robustness campaign), bisecting
  `test/01_unit/compiler/backend/type_mapper_spec.spl`'s "handles composite
  types using each backend strategy" failure (see bonus-find update in
  `doc/08_tracking/bug/wildcard_import_c_backend_stubs_function_to_int_2026-07-30.md`)

## Symptom

```simple
val pairs = [("count", 1), ("ready", 2)]
val out = pairs.map("{_.0}: {_.1}")
```

fails with:

```
semantic: variable `__p1` not found
```

Reproduced standalone in a fresh single-`it`, single-`describe` spec file
with zero other imports/tests (rules out test-state leakage across `it`
blocks or files):

```simple
describe "probe4 isolated":
    it "two bare placeholders different index no call, isolated file":
        val pairs = [("count", 1), ("ready", 2)]
        val out = pairs.map("{_.0}: {_.1}")
        expect(out.join(", ")).to_equal("count: 1, ready: 2")
```

`bin/simple test --no-session-daemon <that file>` → `Results: 1 total, 0
passed, 1 failed`, same `variable __p1 not found` message.

## Bisection (all against `bin/release/x86_64-unknown-linux-gnu/simple`, 2026-07-30)

| shape | result |
|---|---|
| `pairs.map("{_.0}")` (single bare placeholder) | PASS |
| `pairs.map("{_.1}")` (single bare placeholder) | PASS |
| `pairs.map(_.0)` (bare shorthand, no template at all) | PASS |
| `pairs.map("{double(_)}")` (single placeholder, wrapped in a call) | PASS |
| `pairs.map("{_.0}: {_.1}")` (TWO bare placeholders, no call) | **FAIL** — `variable __p1 not found` |
| `pairs.map("{_.0}-{_.0}")` (same index used twice) | **FAIL** — `variable __p1 not found` |
| `["a","b"].map("{_}-{_}")` (no `.0`/`.1` at all, just two bare `_`) | **FAIL** — `variable __p1 not found` |
| `pairs.map("{_.0}: {double(_.1)}")` (second placeholder wrapped in a call) | **FAIL**, but with a DIFFERENT message — `cannot convert function to int` (this is the OTHER, separate bug — see below) |

So the minimal failing shape needs no tuple indexing, no nested call, and no
method call at all — just the SAME bare `_` identifier appearing twice inside
one template's `{...}` regions. This is a distinct bug from the one fixed
alongside it in `wildcard_import_c_backend_stubs_function_to_int_2026-07-30.md`
(that one requires a nested call/method-call argument and fails with
"cannot convert function to int" / "cannot access field on value of type
function" — a lambda value reaching a plain-value parameter — and IS fixed).
This one fails with an unresolved-name error instead, meaning something
really does try to bind/read a second lambda parameter (`__p1`) that is never
supplied.

## Why the obvious mechanism does not explain it (dead ends recorded so the
## next investigator doesn't retrace them)

`__p0`/`__p1`-style names are generated in exactly one place in the whole
compiler: `src/compiler/10.frontend/desugar/placeholder_lambda.spl`
(`transform_placeholder_lambda`/`replace_placeholders`, string patterns
`"__p{i}"` and `"__p{_ph_counter}"` and `"__p{param_idx}"`). Verified via
repo-wide grep (`grep -rn '__p[0-9]\|"__p"' src/compiler`) that no other file
anywhere generates this naming pattern, by any concatenation form. So the
`__p1` reference MUST originate from that module's logic somehow being
invoked on this template.

`transform_placeholder_lambda` is itself only ever CALLED from 3 sites (grep
`transform_placeholder_lambda(` repo-wide): two pipe-operator (`|>`) call
sites in `parser_expr.spl`, and `parse_call_arg()`
(`src/compiler/10.frontend/core/parser_expr.spl:657`), which runs on every
call/method-call argument in the language.

But the two bare regions `_.0` and `_.1` in `"{_.0}: {_.1}"` are NOT call
arguments — they are parsed via a completely separate path:
`_FlatAstBridge/convert_nodes.spl:flat_bridge_build_string_interps` splits the
literal on top-level `{...}` regions and, for each one, calls
`flat_bridge_parse_interp_inner(inner)`, which does a **fresh**
`lex_init_with_path(inner.trim(), "")` + `parser_advance()` + `parse_expr()`
— NOT `parse_call_arg()`. `parse_expr()` → `parse_pipe()` → ... → `parse_primary()`
for a bare `_.0` (identifier + field access, no parens) never reaches
`parse_call_arg` at all when there is no nested call in the region. Static
tracing therefore predicts these two regions should come out as plain,
unrenamed `Ident("_")` nodes (this DOES appear to be what happens for the
single-placeholder-per-template cases, which all pass). Yet the double-bare
case reproducibly fails referencing `__p1` — a contradiction with the static
trace that was not resolved in this lane.

Also checked and ruled out:
- `expr_interpolated_string()` (the constructor for the flat-arena
  `EXPR_INTERPOLATED_STRING` tag, which `placeholder_lambda.spl`'s own
  `EXPR_INTERPOLATED_STRING` case in `count_placeholders`/`replace_placeholders`
  DOES recurse over multiple `parts` with a shared counter — which WOULD
  reproduce exactly this bug if reachable) is constructed in exactly one place
  repo-wide: inside `replace_placeholders` itself. No other code builds this
  node, so (as far as static grep can show) that code path is never actually
  fed a fresh `EXPR_INTERPOLATED_STRING` from outside — but this is the
  single most likely site if some other construction path was missed.
- HIR lowering (`20.hir/hir_lowering/expressions.spl`, `lower_interpolation_list`)
  and MIR lowering (`50.mir/_MirLoweringExpr/expr_dispatch.spl`,
  `split_interpolation_segments`/`lower_string_interpolation`) both only
  consume an already-built `interps`/`HirInterpolation` list generically; no
  `_`/placeholder-aware logic found there.
- Ruled out cross-test/file state leakage from `_ph_counter` (a module-level
  var in `placeholder_lambda.spl`) by reproducing in total isolation (single
  `it`, single `describe`, single file, zero other imports).

## Suggested next step

Since a rebuild of the self-hosted binary is required to test any fix (see
the sibling doc's "Not yet verified" note — same constraint applies here),
the fastest way to actually resolve this without more blind static tracing is
to add a temporary `eprint` at the top of `transform_placeholder_lambda` (and
at `expr_interpolated_string`'s one call site) showing `eid`/`tag`, rebuild
once, and run the isolated repro above to get a real call trace instead of
guessing further from source reading alone.

## Workaround

None found that keeps the placeholder form. Rewrite as an explicit lambda:
`pairs.map(\p: "{p.0}: {p.1}")` instead of `pairs.map("{_.0}: {_.1}")`.
