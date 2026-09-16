# Bug: `skip` reserved token cannot be used as a struct field name

## Triage 2026-09-13 — STILL OPEN, reproduced; fix is in the lexer and blocked here
- **measured** — `struct S: skip: bool / n: i64` still fails to parse under `bin/simple run`
  (Rust seed v1.0.0-rc.1, Windows): `Unexpected token: expected identifier, found Skip`.
- **inferred** — the fix belongs in lexer/parser code under `src/compiler/**` and
  `src/compiler_rust/**`, which this triage pass must not edit (a bootstrap is running
  concurrently). Left OPEN — fix blocked by concurrent bootstrap, not by difficulty.

- **Id:** skip_reserved_token_blocks_struct_field_2026-06-15
- **Severity:** P3 (workaround: rename field)
- **Filed:** 2026-06-15
- **Area:** parser / lexer (reserved keywords)

## Summary
A struct field literally named `skip` fails to parse. `skip` is the SSpec test
directive (`skip(...)`), and the lexer emits a `Skip` token for the bare
identifier even in a struct field declaration position, where only an identifier
is expected.

## Reproduction
```simple
struct Pattern:
    bytes: [u8]
    skip: [i64]
```
Error:
```
parse: Unexpected token: expected identifier, found Skip
```
(observed building `src/lib/common/search/types.spl` Pattern's bad-character
skip table for Boyer-Moore-Horspool.)

## Workaround applied
Renamed the field to `skip_tbl` (and local `skip` var to `tbl`). The prefixed
identifier `skip_for` (a method) parses fine — only the bare `skip` token is hit.

## Suggested fix
`skip` should be context-sensitive: treat it as the test directive only at
statement position inside an `it`/`describe` block, not as a globally reserved
token. Several other words have the same problem (`gen`, `val`, `unit`,
`pass_out`, `kernel`, `trace`) — a general "soft keyword in non-directive
position" pass would cover the family.
