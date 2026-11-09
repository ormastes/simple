# Promote W-STR-BRACE-001 from warning to error (and migrate the corpus)
**Date:** 2026-11-09
**Severity:** P3
**Status:** open
**Related:** `interp_brace_literal_collides_with_string_interpolation_2026-07-03`

Owner decision: a `{...}` in a double-quoted string that is not a valid
interpolation must be a compile/lex error suggesting `{{` / `}}`. It landed as
warning `W-STR-BRACE-001` (verbatim-literal value kept) because the corpus has
15,033 such sites (measured 2026-11-09 with the ignored seed test
`brace_corpus_scan`, `BRACE_SCAN_ROOTS=src,test`): about 4,535 unmatched/lone
`{`, about 10,500 non-expression groups (CSS, JSON, awk).

To do: codemod the sites to `{{`/`}}` (or raw strings), then flip `warn_brace`
(seed `lexer/strings.rs`, `literals.rs`) and `interpolation_note_malformed_region`
(self-hosted `string_interpolation_expand.spl`) to errors. A lone `}` stays
accepted unless the owner extends the rule.
