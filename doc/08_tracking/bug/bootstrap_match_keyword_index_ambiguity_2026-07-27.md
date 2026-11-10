# Bootstrap Parser Misreads `match[0]` As A Match Expression

- **Date:** 2026-07-27
- **Area:** pure-Simple parser / keyword identifiers
- **Severity:** high — blocks the strict Stage 4 full-CLI bootstrap.
- **Status:** OPEN.

## Reproduction

```simple
val match = [7, 9]
val first = match[0]
```

The pure-Simple parser accepts the G26 keyword binding, then reports
`expected :, got Newline` on `match[0]`. `parse_primary_expr` consumes
`match` as the match-expression introducer because `g33_kw_ident_follow`
does not include `[`, which can also begin a valid match scrutinee.

## Required Fix

Use token adjacency to disambiguate the forms: `match[0]` must remain keyword
identifier postfix indexing, while spaced `match [0]: ...` must remain a match
expression. Add one focused parser regression for both forms. Until then,
Stage 4 sources use non-keyword local names such as `match_result`.

## Evidence

Strict bootstrap checkpoint `f461c1cb248150a116c05b95b42a0ba23b9a218c`
failed in `src/std/nogc_sync_mut/compression/gzip/lz77.spl:105` while parsing
`val distance = match[0]`.

## Triage 2026-11-10 (p3-boot2 lane)

SUPERSEDED — the required fix (token-adjacency disambiguation) is implemented
and spec-covered on work/p3-boot2-20261110 (base origin/release/1.0.0),
landing 2026-11-07 in `9e7e7a526edb` (PR #7597):

- Statement position: `src/compiler/10.frontend/core/parser_stmts.spl:1030-1031`
  — `adjacent_index = kind == TOK_LBRACKET and par_line_get() == match_line
  and par_col_get() == match_col + 5`; `match[0]` routes to identifier +
  postfix indexing, spaced `match [first]:` stays a match statement.
- Expression position: `src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl:1196-1197`
  — the same adjacency test; `val first = match[0]` parses as EXPR_INDEX on
  the identifier, `val r = match n: ...` still builds a genuine
  expr_match_expr.
- Focused regression spec: `test/01_unit/core/parser_ce_keyword_identifier_spec.spl:74-88`
  drives this record's exact reproducer (`var match = [10, 20]`,
  `val first = match[0]`, `match[0] = 30`, spaced `match [first]:`) and
  asserts EXPR_INDEX with left ident "match".
- Interim guard `sh scripts/check/check-keyword-identifier-bindings.shs` ->
  `PASS — 44958 .spl file(s) checked` (no FATAL keyword bindings under src/;
  the guard documents `var match` as G33-sanctioned and spec-tested).

Current designed behavior note: `val match = ...` is now REJECTED by both
parsers (reserved keyword as val binding name — the seed prints exactly that;
the self-hosted checked entry returns has-errors, asserted in the same spec
at :131/:135). This record's reproducer shape is therefore rejected one step
earlier than it was in 2026-07-27; the `match[0]` ambiguity itself is what
the adjacent_index arm fixes for G33-sanctioned `var match`.

Verification gap (not a parser-behavior failure): the regression spec cannot
EXECUTE under this lane's Rust seed — every spec importing `core.parser`
fails at semantic setup with "variable `par_state` not found" (measured on
this spec and independently on
`test/01_unit/core/index_bracket_validation_spec.spl`), a seed-JIT gap
compiling the current `src/compiler/10.frontend/core/parser.spl` module-level
state. Executable verification needs the self-hosted binary (heavy build,
outside this lane's grant). Source-level fix + spec + grep gate are the
cited evidence.
