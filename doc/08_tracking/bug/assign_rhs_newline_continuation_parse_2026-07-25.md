# `name =` with the RHS on the next line does not parse — took a whole example file down silently

- **ID:** assign_rhs_newline_continuation_parse_2026-07-25
- Status: OPEN (P3)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  classifies assignment tokens as RHS-requiring; deployed Stage2/old Stage3
  artifacts still reject the form
- **Severity:** high — the failure is whole-file (nothing in the module loads) and the
  diagnostic names no line, so the cost to locate it is a manual bisect

## Symptom

```
error: compile failed: parse: in ".../examples/06_io/ui/web_render_file_gui.spl":
Unexpected token: expected expression, found Newline
```

No line, no column, no caret. The file is 548 lines; locating the offending token
required bisecting by prefix truncation (`head -n N` + parse) — 20+ compiler
invocations.

## Historical cause

An assignment whose right-hand side starts on the following line:

```
current_font_pixel_size =
    updated_result.vector_font_pixel_size
```

The deployed compiler did not continue a bare assignment after trailing `=`,
so the parser reached a Newline where it wanted an expression.

There were **10** such splits, lines 471-491, all introduced together as
column-width wrapping.

## Impact observed

`examples/06_io/ui/web_standards_showcase_gui.spl:14` does
`use web_render_file_gui.{run_web_standards_showcase, ...}`, so the unparseable
module took the entire web-standards showcase child down with it. The `web × host-WM`
showcase-matrix cell could therefore never produce a frame — the child died at parse
before rendering anything. This was masked because the parent wrapper's own failure
surfaced only as a generic example-watchdog timeout.

## Why it was not caught

Nothing parses `examples/**` in CI. The file was committed in this state; `bin/simple
lint` on it exits non-zero but does not print the parse error, so lint gave no signal
either.

## Current source and artifact status (2026-07-29)

Commit `ab63c351d142` made every assignment token RHS-requiring in
`token_requires_rhs`; both live lexer paths now suppress layout after trailing
`=`, compound assignment, and walrus. The existing parser continuation spec
now covers bare, field, compound, and walrus assignments.

The genuine deployed Stage2 (`58c2827c…`) and retained old Stage3
(`98087781…`) both still reject the focused probe at its trailing `=`. A
single current-source Stage3 production attempt emitted no progress for three
minutes and was terminated; no full bootstrap or seed fallback was attempted.
The JS reclamation and BrowserSession animation binaries therefore remain
blocked on compiler artifact refresh, not source grammar.

## Remaining work

1. **Point at the token.** The parse error must carry file:line:col + caret, like the
   other diagnostics do. This alone turns a multi-hour bisect into a 5-second read,
   and is the highest-value change here.
2. **Make `lint` report parse errors.** `bin/simple lint <file>` currently exits 1 on
   an unparseable file while printing only unrelated style info. A linter that cannot
   say "this does not parse" fails at its first job.
3. **Parse-gate `examples/**`** in CI so an unparseable example cannot land.
4. Produce and admit a fresh pure-Simple Stage3 compiler containing
   `ab63c351d142`, then rerun the focused assignment probe once.

## Related

Same day, same class of "silent wrong thing, no diagnostic":
`doc/08_tracking/bug/env_get_nil_coalesce_dead_fallback_2026-07-25.md` (`??` applied
to a non-optional is provably dead code and warns about nothing).

**2026-07-31 clarification:** the fix referenced above (`ab63c351d142`) only
touched the pure-Simple self-hosted lexer
(`src/compiler/10.frontend/core/{lexer_scanners,lexer_struct,tokens}.spl`).
The **Rust seed parser** (`src/compiler_rust/parser`) had the identical
surface symptom as a separate, unrelated defect in a separate parser
implementation, still present as of `92dc586924a` (2026-07-31) and fixed in
`doc/08_tracking/bug/seed_assignment_trailing_equals_continuation_2026-07-31.md`.
Don't assume "SOURCE FIXED" here covers the seed.

## 2026-08-17 content triage (w0001 ZCLAIMED, source-inspection only)

Verdict: ALREADY-FIXED (pure-Simple source side)

Corrected location: `src/compiler/10.frontend/core/tokens.spl:543` (NOT `core/lexer.spl`, which only mentions `token_requires_rhs` in a comment at :608).

```spl
fn token_requires_rhs(kind: i64) -> bool:          # tokens.spl:532
    ...
    if kind >= TOK_ASSIGN and kind <= TOK_WALRUS:  # tokens.spl:543
        return true
```

Assignment tokens ARE classified RHS-requiring, so `name =` followed by a
newline continues instead of erroring. NOT PROVEN: behaviour of already-deployed
Stage2/Stage3 artifacts (no build/run was performed in this triage).
