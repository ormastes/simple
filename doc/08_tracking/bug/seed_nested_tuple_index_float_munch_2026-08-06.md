# Rust seed: nested tuple index `r.0.1` lexes as a float and fails to parse

- **Filed:** 2026-08-06
- **Status:** FIXED both halves (seed half 2026-08-17). Seed fix:
  `split_tuple_index_pair` +the `TokenKind::Float` arm in
  `src/compiler_rust/parser/src/expressions/postfix.rs` (mirrors the
  pure-Simple `tuple_index_pair_split`), with Rust unit tests
  (`mod tuple_index_split_tests`, same file) and a seed-lane spec
  `test/01_unit/compiler/frontend/nested_tuple_index_seed_parser_spec.spl`.
  Re-verified RED before the fix on the deployed seed:
  `error: compile failed: parse: ... Unexpected token: expected identifier,
  found Float(0.1)`.
  The re-split works on the token LEXEME, not the parsed `f64`: `.0.1` and
  `.0.10` share the value `0.1`, so an f64-based split cannot distinguish
  index 1 from index 10. Only an exact `digits.digits` lexeme is
  reinterpreted, so `1e3` / `0.1f32` / `.5` / `1.` stay floats.
  The pure-Simple half was already FIXED — see
  `src/compiler/10.frontend/core/parser_expr.spl`
  (`tuple_index_pair_split`) and
  `test/01_unit/compiler/frontend/nested_tuple_index_parse_spec.spl`.
- **Component:** `src/compiler_rust/parser` (bootstrap seed)

## Reproduction

```
$ cat repro2.spl
val r = ((1, 2), 3)
println(r.0.1)

$ bin/simple run repro2.spl
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
error: compile failed: parse: in "repro2.spl": Unexpected token: expected identifier, found Float(0.1)
```

`bin/simple` currently resolves to
`bin/release/x86_64-unknown-linux-gnu/simple`, which self-identifies as the
Rust-built seed — so the message above is the **seed** parser, not the
pure-Simple one. The pure-Simple parser had the same defect with a different
message (`expected field name after '.'`); that one is now fixed.

Workaround in user code today: bind an intermediate `val` and index one level
at a time. Repo policy forbids normalising that, hence this file.

## Root cause

Maximal-munch tokenization. Nothing re-splits the token afterwards.

1. `src/compiler_rust/parser/src/lexer/numbers.rs:195-225` — after scanning the
   integer part, the scanner takes `.` + digit as a float regardless of what
   preceded the number. Source `r.0.1` therefore lexes as
   `Ident("r")`, `Dot`, `Float(0.1)` — never `Dot Int Dot Int`.
2. `src/compiler_rust/parser/src/expressions/postfix.rs:347-374` — the `Dot`
   arm handles `TokenKind::Integer(n)` (tuple index), `LParen` (computed field)
   and otherwise calls `expect_method_name()`. There is no `Float` arm, so the
   float token reaches `expect_method_name` and produces the error above.

## Fix (not yet applied — see "Why not landed here")

Mirror the pure-Simple fix: in the `Dot` arm of `postfix.rs`, when the current
token is `TokenKind::Float`, re-split its **lexeme** on `.` and, if it is
exactly `<digits>.<digits>`, emit two chained `Expr::TupleIndex` nodes.

The lexeme is available: `Token` carries `pub lexeme: String`
(`src/compiler_rust/parser/src/token.rs:532`). Reading the lexeme rather than
the decoded `f64` is load-bearing — `r.0.10` and `r.0.1` share the same f64
payload, so an f64-based split would silently produce index 1 for `r.0.10`.
A silent wrong index is worse than the current parse error.

Reject anything that is not exactly `<digits>.<digits>` (e.g. `0.1e2`) so those
keep reporting rather than mis-indexing.

Blast radius: the branch is reachable only where the parser currently raises a
hard error, so it cannot change the meaning of any program that parses today.
Float literals are untouched because the lexer is not modified.

## Why not landed here

Changing `src/compiler_rust/parser` requires a cargo rebuild of the seed to
validate, and both the build and a full bootstrap were in use by other lanes at
the time of writing. Landing unverified Rust into the seed risks breaking
`--full-bootstrap` for every concurrent session. The pure-Simple half was
landed and verified instead; this file records the remaining half with the
exact call sites so the seed change is mechanical.

## Verification for the pure-Simple half (done)

`bin/simple test test/01_unit/compiler/frontend/nested_tuple_index_parse_spec.spl`

- parser_expr.spl at `origin/main`: `Results: 13 total, 9 passed, 4 failed`
  (`[parser_error] line 2:14: expected field name after '.'`)
- with the fix: `Results: 13 total, 13 passed, 0 failed`
- reverted again (sabotage): back to `9 passed, 4 failed`, same 4 examples

The nine regression-guard examples (`1.0`, `3.14`, `1e5`, `0.0`, `x.0`,
`r.0.name`, `x.method()`, `x.name`, `0..10`) pass both before and after, which
is what proves the re-split did not disturb ordinary float lexing.
