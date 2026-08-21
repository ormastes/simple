# Bug: trailing binary-operator line continuation causes "expected expression, found Dedent"

**ID:** parser_trailing_operator_line_continuation_2026-07-13
**Filed:** 2026-07-13
**Status:** OPEN — narrowed 2026-08-09/10, see "2026-08-09 re-triage" below: the
multi-line-body form of this pattern is already fine; only a single-line body on
the continuation line still reproduces.
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

The staged `rt_value_bool` SFFI boundary normalization clears the reported
unparenthesized `or` continuation failure. The remaining Stage 4 failure is a
separate semantic-resolution bug: `resolve_method -> try_ufcs` selects imported
`nogc_async_mut.path.join(parts: [text])` for `Array.join("")`. MIR therefore
emits the free path join, lexer slices become slash-separated text, and keywords
are parsed as identifiers. A focused semantic regression and the smallest UFCS
suppression for Array/Slice `join` are staged. A fresh bootstrap was not run
because the three-cycle cap had already been reached; Stage 4 remains
unqualified.

## 2026-08-09 re-triage — bug narrows to single-line body after a continued condition

Reproduced fresh with the seed (`bin/simple run`, `bin/release/x86_64-unknown-linux-gnu/simple`,
current `bin/simple` deployment) against isolated repro files, binary-searching the
doc's own minimal repro to find exactly which part still fails:

- `if a or\n   b:\n    return true` — **multi-line indented body** — **PARSES FINE**.
- `a and\n    b` as a bare trailing statement — **PARSES FINE**.
- `if a or\n   b: return false` — **single-line body on the same source line as
  the continuation** — **STILL FAILS**: `Unexpected token: expected expression,
  found Dedent`. Confirmed this is independent of the `== None`/`== nil`
  comparison in the original repro (a bare `bool` operand reproduces identically)
  and independent of `and` vs `or`.

So the fix already landed for `sfnt.spl`-style code (multi-line indented bodies)
and for bare trailing-operator statements, but the parser still cannot handle a
condition that spans lines AND resolves to a single-line (colon-suffixed,
same-line) body. This is a narrower defect than the original filing described:
the trailing-operator continuation itself works; what fails is specifically the
lexer/parser's indent-tracking when the continuation's dedent-then-colon
transitions straight into inline-statement mode instead of an indented block.

**Not fixed this pass.** Root-causing this requires tracing the lexer's
indent/dedent token stream across the continuation boundary in
`src/compiler/10.frontend/core/lexer*.spl` and the `if`-statement grammar's
single-line-body arm in `src/compiler/10.frontend/core/parser_stmts.spl`, then
verifying no regression across the parser spec suite — a properly-scoped follow-up
given this session's remaining verification budget only covered isolated repro
files, not a parser-spec regression sweep. Left OPEN with this narrower
characterization rather than guessing at a grammar fix.

Repro files used (not checked in): `if a or / b: return false` style single-line
variants confirmed failing; `if a or / b:\n return true` (indented block) and
bare `a and / b` confirmed passing, on `bin/simple run` with the current
`bin/release/x86_64-unknown-linux-gnu/simple` seed.

## 2026-08-21 re-verification (seed `bin/simple`, still OPEN, single-line body only)

Bisected six variants; exactly one shape fails, confirming the 2026-08-09
narrowing. Multi-line bodies pass regardless of `not`, 3-way chains, `==`/`>`
operands, or text/int operands:

```
# FAILS — "Unexpected token: expected expression, found Dedent"
fn f(a: bool, c: text) -> i64:
    if a or
            c == "": return 1
    2

# PASSES — identical condition, body on its own line
fn f(a: bool, c: text) -> i64:
    if a or
            c == "":
        return 1
    2
```

Live instance in the tree: `src/compiler/00.common/assurance/formal_delivery_gates.spl:147-149`
and `:205-207` (`release.bundle_hash == "": return FormalDeliveryDecisionV1(`),
which is why `formal_delivery_gates_spec.spl` reports `executed=0` under the
seed. The pure-Simple frontend (`parse_full_frontend`) accepts both forms —
the any-escape census lowers that file with 0 unanalyzable — so this is
seed-parser-only (`src/compiler_rust/parser`, owned by another lane; not
edited here). It is unrelated to the any-escape census false positives
(see `any_escape_census_undercounts_2026-08-21.md`, same day).
