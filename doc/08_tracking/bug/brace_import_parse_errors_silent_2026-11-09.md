# brace_import_parse_errors_silent_2026-11-09 (P2)

**Report:** `parse_module_silent_checked` returned `false` (no error) for any
source starting with a brace import such as `use foo.{X}`, even when a syntax
error followed.

**Root cause:** not in the parser. The fixture was written as a double-quoted
literal, `"use foo.{X}\n..."`. In Simple, `{X}` inside `"..."` is string
interpolation (same class as
`interp_brace_literal_collides_with_string_interpolation_2026-07-03`), so the
parser never received a brace import. Under the seed the spec fails with
`semantic: variable X not found` before reaching the parser.

**Evidence:** `test/01_unit/compiler/frontend/brace_import_parse_error_spec.spl`.
- RED, double-quoted fixture: 3/5 pass, 2 fail with `variable X not found`.
- GREEN, raw `'use foo.{X}'` fixture, with no `src/` change: 5/5 pass. Both
  error cases return `true`, and the valid brace-import module returns `false`.
- Seed parser: `use std.text.{trim}` followed by `fn f( -> :` is rejected with
  `Unexpected token: expected identifier, found Arrow`.
- Unchanged: `parser_silent_trace_contract_spec` passes 6/6 and
  `match_case_fat_arrow_spec` passes 9/9.

**Fix:** a prevention spec using raw-literal fixtures. No parser change.
