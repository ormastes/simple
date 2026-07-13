# Bug: trailing binary-operator line continuation causes "expected expression, found Dedent"

**ID:** parser_trailing_operator_line_continuation_2026-07-13
**Filed:** 2026-07-13
**Status:** WORKED AROUND (source rewritten); parser gap NOT fixed
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
