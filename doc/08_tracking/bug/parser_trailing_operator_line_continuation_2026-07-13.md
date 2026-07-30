# Bug: trailing binary-operator line continuation causes "expected expression, found Dedent"

**ID:** parser_trailing_operator_line_continuation_2026-07-13
**Filed:** 2026-07-13
**Status:** SOURCE FIXED — refreshed Stage2/RV64 verification pending
**Severity:** P2 — silently-confusing parse failure on a plausible/idiomatic form
**Component:** Rust discovery parser equality/comparison continuation

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

The staged `rt_value_bool` SFFI boundary normalization clears the reported
unparenthesized `or` continuation failure. The remaining Stage 4 failure is a
separate semantic-resolution bug: `resolve_method -> try_ufcs` selects imported
`nogc_async_mut.path.join(parts: [text])` for `Array.join("")`. MIR therefore
emits the free path join, lexer slices become slash-separated text, and keywords
are parsed as identifiers. A focused semantic regression and the smallest UFCS
suppression for Array/Slice `join` are staged. A fresh bootstrap was not run
because the three-cycle cap had already been reached; Stage 4 remains
unqualified.

## 2026-07-30 Rust discovery fix

Fresh Stage2 RV64 entry-closure discovery exposed the same missing continuation
at `window_scene.spl:444:39` and `simple_web_window_renderer.spl:235:73`:
`Unexpected token: expected expression, found Newline`.

The generated binary-precedence parsers already skip newline/indent after a
trailing operator. The hand-written Rust `parse_equality` and
`parse_comparison` paths did not. Both now call the same shared continuation
helper after consuming their operator. The existing native-project discovery
test uses multiline `==` and `>` expressions and passes. Closure audit found
21 affected RV64 equality sites covered by this root fix. Closure requires a
fresh seed and Stage2 before this bug can close.
