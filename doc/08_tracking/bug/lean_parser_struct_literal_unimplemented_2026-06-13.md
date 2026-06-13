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
- **Status:** OPEN (diagnosed, fix deferred to its own focused task)

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
field-parsing shape of the dict path (`parser_primary_part2.spl:563`). MUST
disambiguate `{` carefully — dict literal (`{ k: v }`), struct literal (`Name { k: v }`),
and block bodies all use `{`/indentation. Per memory `feedback_struct_literal_brace_syntax`:
allowlist the `ident {` struct form, never "any ident + `{`". After the primary-level
rule exists, `parse_call_arg_raw`'s manual ident path inherits it (or route the
non-named-arg ident case back through the struct-literal check). Verify with the
g49 probe + a re-sweep; watch for regressions in dict-literal and block parsing.

## Related deferred gap classes (from the same 2026-06-13 per-file sweep)
- **Generator expression as call arg** `total(x for x in xs)` (no brackets) →
  errors=true (`expected :, got for`). Niche. List-comp `[x for x in xs]` is fine.
- **`extern class Name:`** declaration form (`extern fn` works, `extern class`
  does not) — 2 src/lib sites (error.spl SimpleError).

## Context
Surfaced after the env-mirror perf fix made per-file `check` linear (see
`interp_parse_superlinear_2026-06-12.md`). Dominant gap classes G47 (`else if`,
1001 sites) and G48 (colon-inline ternary, ~29 sites) already fixed; ~23/24
sampled src/lib files parse clean. This is part of the remaining long tail.
