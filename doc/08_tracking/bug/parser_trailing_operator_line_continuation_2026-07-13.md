# Bug: trailing binary-operator line continuation causes "expected expression, found Dedent"

**ID:** parser_trailing_operator_line_continuation_2026-07-13
**Filed:** 2026-07-13
**Status:** OPEN — self-hosted dynload recurrence confirmed on 2026-07-23
**Severity:** P2 — silently-confusing parse failure on a plausible/idiomatic form
**Component:** compiler frontend / parser (both the deployed self-hosted `bin/simple`
and the fresh Rust seed reject the same input)

## Symptom

An unparenthesized boolean/binary expression that continues onto the next line by
ending the line with a trailing operator (`or`, `and`, etc., with no wrapping
parens) fails to parse with:

```
error: parse: Unexpected token: expected expression, found Dedent
```

## Minimal repro

```simple
fn f(a: bool, b: bool) -> bool:
    if a == None or
       b == None: return false
    a and
        b
```

Note `doc/07_guide/quick_reference` / `.claude/rules/language.md` documents that
**parenthesized** multi-line booleans work (`if (a and\n b):`) — only the
*unparenthesized* trailing-operator form is affected.

## Affected file (fixed in this change)

- `src/lib/common/encoding/sfnt.spl` (`_sfnt_names_match`, was lines ~280-284):
  rewrote the trailing `or`/`and` continuations into single-line `if` statements
  plus intermediate `val` bindings, preserving short-circuit order and semantics.
  No other files in this repo currently match the pattern (`grep -nE
  '(\bor|\band)\s*$'` across `src/lib/common/encoding/` found only this file).

## Requested fix

Either:
1. Support trailing-binary-operator line continuation in the grammar (treat a
   line ending in a binary operator as an implicit continuation, symmetric with
   the already-supported parenthesized form), or
2. If unsupported by design, replace the generic "expected expression, found
   Dedent" with a targeted diagnostic (e.g. "line ends with binary operator —
   wrap the expression in parentheses to continue on the next line").

## Verification

`bin/simple check src/lib/common/encoding/sfnt.spl` no longer reports the Dedent
parse error after the rewrite (only the known unrelated `unknown extern
function: rt_cli_arg_count` semantic message remains).

## 2026-07-23 recurrence

Stage 4 fails on an unparenthesized `or` continuation in
`src/app/devhub/main.spl` even though the Core lexer rule and
`dedent_continuation_spec.spl` already cover it. Rebuilding Stage 2 and Stage 3
with kind-only handling for unique `TOK_KW_AND` and `TOK_KW_OR` did not change
the failure, so token-text comparison is not the cause and that experiment was
reverted. A focused native probe then showed `core_lexer_next_token` correctly
emitting `true`, `or`, `false` without layout tokens, while parser-facing
`lex_next` recorded continuation state after `or` and emitted `NEWLINE`,
`INDENT` on its next call. Routing through the state-in/state-out helper did not
change that result. A dedicated Boolean mirror also failed because assignment
back into the copied `CoreLexer` is itself unreliable in this path; that
experiment was reverted. The next scoped fix should derive continuation inside
`core_lexer_next_token` from the surviving previous `cur_kind`/`cur_text`, then
rerun the native probe before another staged bootstrap.
