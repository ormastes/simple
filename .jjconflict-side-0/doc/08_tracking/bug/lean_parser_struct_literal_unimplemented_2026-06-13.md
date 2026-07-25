# Lean parser: struct-literal `Name { field: value }` is unimplemented

- **ID:** lean_parser_struct_literal_unimplemented
- **Severity:** P1 (parser gap class; ~50 direct sites / 19 src/lib files, but
  IMPORT-AMPLIFIED: a struct-literal in a shared imported module errors for every
  file that imports it. A 24-file common/+nogc_sync_mut/ sample post-G47 showed
  11 clean / 13 errored — almost all 13 on this gap, many with an identical
  `167:58 expected ), got {` from a common imported module. This is the dominant
  remaining src/lib parse blocker. NOTE: likely also needs flat_ast_bridge
  support for EXPR_STRUCT_LIT — verify the bridge converts it, since the parser
  never produced it before.)
- **Date:** 2026-06-13
- **Component:** `src/compiler/10.frontend/core/` lean parser
- **Status:** FIXED 2026-06-13 (commit 1cfdeae4f789) — see "Fix landed" below.

## Symptom
Struct-literal brace syntax `Name { x: 1, y: 2 }` is not parsed into a struct
literal. Confirmed via seed probe (`tmp/site12/g49_diag.spl`):
- `g(Name { x: 1, y: 2 })` (positional call arg) → **errors=true** (`expected ), got {`)
- `Foo(bar: Baz { x: 1 })` (named-arg struct value, 44 src/lib sites) → **errors=true**
- `val d = Name { x: 1 }` (bare) → errors=false, but this is LENIENT MISPARSE
  (see root cause), not a real struct literal.
- For contrast, these all parse clean: dict arg `h({ "a": 1 })`, inline-if arg
  `k(if c then 1 else 2)`, list-comp arg `take([x for x in xs])`.

## Root cause
`expr_struct_lit` / `EXPR_STRUCT_LIT (27)` exist in `ast_expr_part1.spl:571` but
have **zero callers in the parser** (`grep -rn 'expr_struct_lit(' parser*.spl` is
empty). The parser never recognizes `ident {` as a struct literal. The bare form
"works" only because `Name` parses as an ident and the trailing `{ ... }` is
consumed leniently elsewhere (NOT as a struct literal — the AST is wrong).

In call-argument position the leniency does not apply: `parse_call_arg_raw`
(`parser_expr.spl:548`) for a plain ident builds `expr_ident` then
`parse_postfix_on` + `parse_binary_from` (lines 576-578) — a post-primary path
that has no `{`-struct-literal rule — so the `{` is left and the caller reports
`expected ), got {`.

## Fix sketch (its own task — do NOT rush; brace-ambiguity hazard)
Implement `ident {` → `expr_struct_lit` in the primary/postfix parser, reusing the
field-parsing shape of the dict path (`_ParserPrimary/primary_expr.spl:563`). MUST
disambiguate `{` carefully — dict literal (`{ k: v }`), struct literal (`Name { k: v }`),
and block bodies all use `{`/indentation. Per memory `feedback_struct_literal_brace_syntax`:
allowlist the `ident {` struct form, never "any ident + `{`". After the primary-level
rule exists, `parse_call_arg_raw`'s manual ident path inherits it (or route the
non-named-arg ident case back through the struct-literal check). Verify with the
g49 probe + a re-sweep; watch for regressions in dict-literal and block parsing.

## Fix landed (2026-06-13, commit 1cfdeae4f789)
Added `parse_struct_lit_tail(base)` in `parser_expr.spl`, invoked from BOTH
`parse_postfix` and `parse_postfix_on` loops via a new branch:
`elif (par_kind_get() == 142 and (expr_get_tag(base) == 6 or expr_get_tag(base) == 11))`
(numeric tags 6/11 = EXPR_IDENT/EXPR_FIELD_ACCESS, used directly to dodge the
stage4 imported-const compare bug). Because Simple blocks are colon+indent and
NEVER brace-delimited, `Ident {` in expression position is unambiguously a struct
literal (dict literals start with a bare `{`). The tail loop tolerates comma- and
newline-separated fields (multi-line), empty `{}`, trailing comma, keyword field
names (G25 keyword-as-name), dotted type paths, and nesting. Field entries are
built as `expr_field_access(value, name, 0)` carriers — str=field name, left=value
— which is exactly the layout `_FlatAstBridge/convert_nodes.spl:355` reads (it ignores the
parallel field_values/STMTS list that `expr_struct_lit` also stores; the two were
written inconsistently and never exercised). `parse_call_arg_raw`'s manual ident
path inherits the rule through `parse_postfix_on`.

### Verification
- Probe `tmp/site12/g50_structlit.spl` (counts real EXPR_STRUCT_LIT=27 nodes, not
  just `parser_has_errors`): single / empty / trailing-comma / call-arg / named-arg
  / nested(=2) / kw-field / dotted / multi-line / postfix-chain all produce real
  struct-lit nodes with errors=false. Regressions (dict literal, plain call,
  `a < b`) stay clean with struct_lits=0; must-fail control stays red.
- End-to-end on the stage4 lean frontend (`tmp/site12/g50_e2e.spl`):
  `Point { x: 3, y: 4 }` → `p=3,4` and nested `Box { origin: Point { x: 10, y: 20 }, w: 5 }`
  → `b=10,20,5` at runtime — proves parse → bridge → HIR → typecheck → codegen.
- `src/lib/common/json.spl` (dict/method-heavy) parses clean via lean frontend — no
  regression. `mcdc.spl` struct-lit lines (112–152) now parse; its remaining error
  at line 187 is the SEPARATE default-parameter-value gap (`minimum: f64 = 100.0`),
  not struct literals.
- Stage4 rebuild clean: 770 compiled, 0 failed.

## Related deferred gap classes (from the same 2026-06-13 per-file sweep)
- **Generator expression as call arg** `total(x for x in xs)` (no brackets) →
  errors=true (`expected :, got for`). Niche. List-comp `[x for x in xs]` is fine.
- **`extern class Name:`** declaration form (`extern fn` works, `extern class`
  does not) — 2 src/lib sites (error.spl SimpleError).
- **Default parameter values** `fn f(minimum: f64 = 100.0) -> T:` → errors=true
  (`expected ), got =`). Surfaced in mcdc.spl:187 after the struct-lit fix cleared
  the earlier errors in that file. Now the next gap class to chase in src/lib.

## Context
Surfaced after the env-mirror perf fix made per-file `check` linear (see
`interp_parse_superlinear_2026-06-12.md`). Dominant gap classes G47 (`else if`,
1001 sites) and G48 (colon-inline ternary, ~29 sites) already fixed; ~23/24
sampled src/lib files parse clean. This is part of the remaining long tail.
