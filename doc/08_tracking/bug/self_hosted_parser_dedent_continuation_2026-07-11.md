# Self-hosted parser: trailing-operator continuation fails across a DEDENT

**Date:** 2026-07-11 · **Status:** open (workaround applied at 4 sites; parser fix pending)
**Found:** stage-4 native-build discovery failed on `src/lib/common/ui/access_cli_grammar.spl`
("Unexpected token: expected expression, found Dedent"), blocking the redeploy carrying the
RuntimeDict fix.

## Repro (self-hosted parser only — the Rust seed parses it fine)

```spl
fn make_page(a: text, b: text) -> text:
    val page = "{" +
        a + "," +
        b +
    "}"        # closing token dedented BELOW the continuation indent
    page
```

`build/bootstrap/stage2/.../simple native-build --entry <this>` →
`failed to parse ... expected expression, found Dedent`.
Indenting the closing token to the continuation depth (8 spaces here) parses and links.

## Divergence

The Rust seed's lexer suppresses INDENT/DEDENT inside an unfinished binary expression
(trailing `+` at EOL), so the dedented closing literal still belongs to the expression.
The self-hosted lexer/parser emits the Dedent token and the expression parser stops.
`bin/simple check` (currently delegating to the seed frontend) reports "All checks
passed" for the same file — so check green ≠ stage-4 discovery green until this is fixed.

## Sites normalized (same semantics, closing token moved to continuation indent)

- `src/lib/common/ui/access_cli_grammar.spl` lines ~227/243/259 (json page/document/error)
- `src/app/ui/access_cli.spl` line ~99

Scanner used (finds trailing-`+` lines whose next line dedents):
`awk '/[+]$/{...}' $(git ls-files 'src/**.spl')` — no other owned-source hits.

## Required fix

Self-hosted lexer/parser: while a binary operator ends a line, treat subsequent
INDENT/DEDENT as insignificant until the expression closes (mirror the seed's rule).
Owner: compiler 10.lexer/parser layer. Until fixed, the dedented-close style is legal
per the seed grammar and WILL reappear from peers writing JSON builders.
