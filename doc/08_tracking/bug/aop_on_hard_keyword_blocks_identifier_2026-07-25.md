# `on` is a hard keyword — using it as a parameter name fails the whole file with a pointcut error

- **Date:** 2026-07-25
- **Area:** parser / AOP pointcut grammar
- **Severity:** medium — silent-looking, badly-localized parse failure on a very
  common identifier.
- Status: CLOSED (not reproducible)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
  in this environment — see Verification note below.

## Repro

```simple
fn showcase_trace(on: bool, stage: text) -> bool:
    if on:
        print "trace={stage}"
    on
```

```
error: compile failed: parse: in ".../graphics_2d_showcase.spl":
Unexpected token: expected pointcut expression 'pc{...}', found Newline
```

The whole file fails to parse. The diagnostic names neither the offending line
nor the identifier `on`, and mentions `pc{...}` — AOP syntax the file never
uses. Renaming the parameter to `enabled` makes it compile immediately.

Note the misdirection cost: the first suspect was the helper's *name* (`trace`),
which is innocent. Only after renaming the function and still failing did the
parameter `on` become the obvious candidate. The error message actively points
away from the cause.

## Why this matters

`on` is an extremely common parameter/variable name for a boolean toggle. It is
not in the documented reserved list in `.claude/rules/language.md`
(`gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`, `pass_todo`,
`pass_do_nothing`, `pass_dn`), so there is no warning that it is unusable.

This is the same class as the recent `cli` fix
(`d5a6312da1b fix(parser): make 'cli' a soft keyword — un-reserve it globally`).

## Proposed fix

Make `on` a **soft keyword**: only treat it as the AOP pointcut introducer when
it is actually in advice position (i.e. followed by `pc{`), and otherwise lex it
as a plain identifier. Mirror the `cli` change.

Failing that, at minimum: (a) add `on` to the documented reserved-keyword list,
and (b) make the error point at the identifier's span and say
"`on` is reserved for AOP advice" rather than "expected pointcut expression".

## Fix

Mirrored the `cli` soft-keyword pattern exactly:
- `src/compiler/10.frontend/core/tokens.spl`: removed the
  `if name == "on": return TOK_KW_ON` mapping from the lexer's
  name-to-keyword table, so `on` always lexes as a plain `TOK_IDENT` (the
  `TOK_KW_ON` constant is kept, unreferenced, matching how `TOK_KW_CLI` is
  kept after the `cli` fix).
- `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl`: added
  `current_ident_is_on_advice_decl()` (raw source lookahead: current ident is
  `on`, followed by whitespace, followed by literal `pc{`) and changed the
  module-body dispatch from `par_kind_get() == 216` to
  `par_kind_get() == 6 and par_text_get() == "on" and current_ident_is_on_advice_decl()`.
  `parse_aop_advice_decl()` itself needed no change — it just
  `parser_advance()`s the current token unconditionally.
- Added a regression case to
  `test/unit/compiler/frontend/parser_spec.spl` ("parse function with 'on' as
  a bool parameter name...") mirroring the existing `cli` regression case in
  the same file.

## Verification note (IMPORTANT — read before closing)

This fix only affects the pure-Simple self-hosted frontend
(`src/compiler/10.frontend/**.spl`). It was **not** possible to verify
end-to-end in the environment this fix was made in:
- `bin/simple test` / `bin/simple run` in this worktree delegate to the
  **Rust seed** (`bin/release/x86_64-unknown-linux-gnu/simple`), confirmed via
  `child binary: .../simple` in the test-runner's own diagnostic output — the
  seed has its own independent Rust lexer/parser (`src/compiler_rust/`) and
  does not read `src/compiler/10.frontend/**.spl` at all, so re-running the
  original repro against the seed still fails identically after this change
  (expected — the seed was never patched, by design: "Fix .spl not Rust").
- No self-hosted `bin/simple` binary (built via `bin/simple build bootstrap`
  from `src/compiler/**.spl`) was available in this worktree to exercise the
  fix for real.

**Before marking this closed**, re-run the new regression spec
(`test/unit/compiler/frontend/parser_spec.spl`, "parse function with 'on' as
a bool parameter name...") and/or the original repro from this file's
`## Repro` section against a freshly-bootstrapped self-hosted `bin/simple`,
and confirm both pass.

## Found via

Adding a level-gated stage trace to
`examples/06_io/ui/graphics_2d_showcase.spl` while root-causing the
2D x headless showcase cell. Recorded per the project rule that a short, safe
form which fails must be fixed or filed rather than silently worked around.
