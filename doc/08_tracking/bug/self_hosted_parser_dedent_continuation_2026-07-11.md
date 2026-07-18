# Self-hosted parser: trailing-operator continuation fails across a DEDENT

**Date:** 2026-07-11 · **Status:** CLOSED — not reproducible against current source; premise
corrected (see "Re-diagnosis" below). Regression spec added:
`test/01_unit/compiler/parser/dedent_continuation_spec.spl`.
**Found:** stage-4 native-build discovery failed on `src/lib/common/ui/access_cli_grammar.spl`
("Unexpected token: expected expression, found Dedent"), blocking the redeploy carrying the
RuntimeDict fix.

## Re-diagnosis (2026-07-11, later same day)

Both halves of the original claim were re-checked directly against current source and turned
out to be wrong:

1. **"The Rust seed parses it fine" — false.** Running the exact repro (and the real
   pre-normalization snippet from `access_cli_grammar.spl`) through
   `src/compiler_rust/target/bootstrap/simple run <file>` — which goes through
   `simple_parser::Parser::new(&source).parse()` in `module_loader.rs`, the same call used by
   `check` — produces the identical `Unexpected token: expected expression, found Dedent`
   error the self-hosted parser gave. `simple_parser` (`src/compiler_rust/parser/`) has no
   lexer- or parser-level rule that suppresses INDENT/DEDENT across a trailing binary operator
   below the continuation indent (`skip_newlines_and_indents_for_method_chain` in
   `parser_helpers.rs:484` only skips `Newline`/`Indent`, never `Dedent`). An earlier `check`
   run that appeared to pass was checking a whole-project scan, not actually validating the
   dedented snippet — it was a false-positive read, not evidence the seed accepts the pattern.
2. **"The self-hosted lexer/parser emits the Dedent and fails" — no longer true (and possibly
   never true against the source that mattered).** The self-hosted lexer
   (`src/compiler/10.frontend/core/lexer_struct.spl`) already has a "G27" rule — see
   `handle_indentation()` around line 777 and the companion newline-suppression around line
   863 — that suppresses Indent/Dedent/Newline emission whenever the previously scanned
   significant token is a binary operator (Plus, Minus, Star, Slash, And, Or, Eq, NotEq, Comma,
   Ampersand, Pipe, Assign). Direct verification: tokenizing the exact repro through
   `compiler.frontend.core.lexer_struct.{make_core_lexer, core_lexer_next_token}` produces a
   flat `String Plus String Plus String Plus String Plus String` run with **no** Indent/Dedent
   token in between; feeding the same source through `compiler.core.parser.parse_module` +
   `parser_has_errors()` returns `false` (no error) for: the dedented-close repro, a
   deeper-than-continuation-indent close, the previously-normalized continuation-indent close,
   and a nested (two-level) version mirroring `access_render_json`. A negative control (a
   genuinely bad indent with no trailing operator) is correctly flagged as an error by the same
   harness, so this isn't a harness that always reports success.
   G27 landed in commit `7c30ce49d04` (2026-07-04, per `git blame` on lexer_struct.spl; an
   earlier draft of this section miscited `c08b1c1fd6`, an unrelated #145 fix for multi-line
   array literals in return position), predating the bug commit `fba693bca8`
   (2026-07-11 15:15 +09) by a week. The
   original stage-4 failure is UNEXPLAINED in detail: deploy lag (a stage-2 binary built from
   pre-G27 source) is one hypothesis, but the bootstrap artifacts from that run have been
   overwritten by peer rebuilds and no discovery-time logs survive, so it cannot be verified.
   What IS verified: today's lexer/parser source handles every tested variant correctly, and
   the Rust seed also REJECTS the dedented style (the original doc's "seed parses it fine"
   premise below is wrong — independently re-tested, including a structural mirror of the
   real access_cli_grammar call sites). No code change was made in this re-diagnosis.

**No further self-hosted lexer/parser change was made.** The 4 call sites normalized in
`fba693bc` remain normalized (both styles now verified to parse); reverting them was out of
scope for this re-diagnosis and is not required since both forms work.

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
