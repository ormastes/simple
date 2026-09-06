# Erlang-style `| pattern -> expr` match arms are documented as preferred but parse nowhere

**Filed:** 2026-09-05
**Severity:** medium — documentation promises a syntax no compiler accepts; 16 tracked files are silently unparseable
**Status:** open
**Area:** parser (Rust seed + self-hosted frontend), language documentation

## Summary

`doc/07_guide/quick_reference/syntax_quick_reference.md` § Pattern Matching
presents two match-arm syntaxes and states:

> **Erlang-style `| ->` is preferred (shorter)**

That form does not parse. Not in the Rust seed, and there is no evidence of it
in the self-hosted frontend either. Only the `case pattern: expr` form — the one
the doc labels "Traditional" — actually works.

## How reproduced

`bin/simple` -> `bin/release/aarch64-unknown-linux-gnu/simple`
(154,560,904 bytes, 2026-09-04 14:46), the Rust seed.

The doc's own verbatim example fails:

```
fn cls(v: i64) -> text:
    match v:
        | 0 -> "zero"
        | 1 -> "one"
        | _ -> "other"

fn main():
    print "r={cls(1)}"
```

```
error: compile failed: parse: Unexpected token: expected LParen, found Newline
```

Every arm shape fails identically — literal patterns, guard patterns
(`| n if n < 0 -> "neg"`), and enum-constructor patterns
(`| Shape.Circle(r) -> r`). Replacing the arms with `case 0: "zero"` etc. makes
the same programs compile and run correctly, so the patterns and bodies are
fine; only the `| … -> …` arm syntax is rejected.

The `expected LParen` wording suggests the parser takes the `->` to be the
function-return-type arrow and then expects a parameter list, i.e. `|` is never
recognised as introducing a match arm at all.

## Scope: 16 tracked files are unparseable because of this

No owned `src/` code uses the form. All in-tree users are the seed-side stdlib
copy under `src/compiler_rust/lib/std/src/tooling/dashboard/` (16 files:
`notify.spl`, `alert_rules.spl`, `collector.spl`, `compare.spl`, `charts.spl`,
`triggers.spl`, `collectors/todo_collector.spl`, `collectors/plan_collector.spl`,
and others), which contain genuine arms such as:

```
| "critical" -> "#ff0000"
| "warning"  -> "#ffaa00"
| _          -> "#0099ff"
```

Those files do not parse:

```
$ bin/simple lint <copy of dashboard/notify.spl>
NOT LINTED: 1 file(s) could not be parsed and were never analysed
Lint failed in 1 file(s)
```

So they are dead weight that no tool can analyse — lint skips them with a
"could not be parsed" line rather than a syntax error naming the construct,
which is how this stayed invisible.

## Self-hosted frontend

`TOK_PIPE` exists (`src/compiler/10.frontend/core/tokens.spl:106`, rendered as
`"|"` at :290) but a grep for `TOK_PIPE`/`TOK_BAR` under
`src/compiler/10.frontend/core/_ParserStmt/` returns nothing, and
`match_type_pattern.spl` has no pipe/arrow arm handling. The token is lexed and
never consumed in arm position. (Not re-verified by execution — no full-CLI
self-hosted binary is deployed — so treat the self-hosted half as a strong
static indication rather than a measured result.)

## Why this is filed rather than fixed

Implementing the arm form is a grammar change, not a bug fix: it needs a
decision on how `|` in arm position is disambiguated from the bitwise-or
operator and from the leading `|` of a multi-pattern alternative, and it would
have to land in the parser consistently across both the seed and the
self-hosted frontend. That is a design decision, so it is recorded here instead
of guessed at.

## Resolution options (pick one — do not leave the doc as-is)

1. Implement `| pattern [if guard] -> expr` arms in both parsers, and keep the
   16 dashboard files as the regression corpus.
2. If the form is not wanted, correct the quick reference (drop the
   "Erlang-style `| ->` is preferred" claim and its examples) and convert the
   16 dashboard files to `case` arms so they parse.

Either way the current state — documented as *preferred*, implemented nowhere,
with 16 unparseable files in tree — should not persist.
