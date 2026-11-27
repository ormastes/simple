# Bug: `skip` reserved token cannot be used as a struct field name
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Triage 2026-11-25 — root cause pinpointed; still OPEN (seed-parser-only gap)

Reproduced on the current deployed binary (`bin/simple.exe`, Rust seed
v1.0.0-rc.1, build-commit `1343b77bbaa`, Windows): the minimal
`struct Pattern: / bytes: [u8] / skip: [i64]` probe still fails with
`parse: Unexpected token: expected identifier, found Skip at line 3, column 5`
(both JIT and interpreter lanes — the error is at parse time, before engine
selection).

Precise root cause, confirmed by source inspection this session:

- The Rust seed parser's general-purpose `expect_identifier()`
  (`src/compiler_rust/parser/src/parser_helpers.rs:952`) accepts dozens of
  soft keywords as identifiers (`val`, `gen`, `kernel`, `pass`, `unit`,
  ...) but has **no `TokenKind::Skip` arm**, so it falls into the
  `_ =>` unexpected-token error. Struct field names route through it via
  `parse_field()` (`src/compiler_rust/parser/src/types_def/mod.rs:436`).
- The sibling helpers `expect_method_name()`/path-identifier helper in the
  same file DO accept `TokenKind::Skip => "skip"` (lines ~1221 and ~1473),
  which is why `skip` works as a method/path name but not as a field name.
- The pure-Simple frontend is NOT affected: `skip` does not appear in its
  keyword table (`src/compiler/10.frontend/core/tokens.spl`,
  `keyword_lookup`), so it lexes as a plain identifier there — same split as
  the already-fixed `case` soft-keyword bug
  (`case_is_reserved_outside_match_2026-08-04.md`).

The bounded fix is one arm in the seed's `expect_identifier()`
(`TokenKind::Skip => "skip".to_string(),`), mirroring the `case` fix. It is
NOT landed here because this lane forbids cargo/Rust builds, so a seed parser
change could not be compiled or verified, and a spec pinning the behavior
would fail under the currently deployed (pre-fix) binary. Left OPEN with the
root cause now exact; whoever next rebuilds the seed can land the one-line
arm plus a `case_soft_keyword_spec.spl`-style spec in the same change.
