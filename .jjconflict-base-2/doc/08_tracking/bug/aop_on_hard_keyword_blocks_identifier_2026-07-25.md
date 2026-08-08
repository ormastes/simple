# `on` is a hard keyword — using it as a parameter name fails the whole file with a pointcut error

- **Date:** 2026-07-25
- **Area:** parser / AOP pointcut grammar
- **Severity:** medium — silent-looking, badly-localized parse failure on a very
  common identifier.
- **Status:** OPEN.

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

## Found via

Adding a level-gated stage trace to
`examples/06_io/ui/graphics_2d_showcase.spl` while root-causing the
2D x headless showcase cell. Recorded per the project rule that a short, safe
form which fails must be fixed or filed rather than silently worked around.
