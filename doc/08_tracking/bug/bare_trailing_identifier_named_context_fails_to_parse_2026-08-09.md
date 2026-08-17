# A bare trailing expression named `context` fails to parse

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Found:** 2026-08-09, Counterpart Conformance Wave 1 lane F4
**Binary:** `bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed; prints the
bootstrap-seed warning banner)

## Symptom

A function whose last statement is the bare identifier `context` does not parse:

```
error: compile failed: parse: in "<file>": Unexpected token: expected expression, found Newline
```

The diagnostic carries **no line or column**, so the failure is only locatable
by bisecting the file with `head -N`.

## Minimal reproduction

Fails:

```
fn a_ctx(registry: ProviderRegistry) -> RunnerContext:
    var context = runner_context(registry, "r", "h", "req")
    context
```

Parses, with no other change:

```
fn a_ctx(registry: ProviderRegistry) -> RunnerContext:
    var c = runner_context(registry, "r", "h", "req")
    c
```

Also parses:

```
    var context = runner_context(registry, "r", "h", "req")
    return context
```

So the trigger is specifically the identifier **`context`** used as the implicit
trailing return expression. `context` is not in the documented reserved-keyword
list (`gen`, `val`, `def`, `exists`, `actor`, `assert`, `join`, `pass_todo`,
`pass_do_nothing`, `pass_dn`), and it is accepted everywhere else — as a
parameter name, as an assignment target, and as a call argument.

## Why this matters

1. It is a silent trap: `context` is the natural name for a runner/session
   value, and the workaround (rename, or add `return`) looks arbitrary.
2. `bin/simple lint` reports the same file **clean, exit 0** — the fail-open
   lint behaviour already filed as
   `lint_reports_clean_on_module_that_fails_to_parse_2026-08-09.md`.
3. The diagnostic has no position, so the cost of finding it is a manual bisect.

## Fix directions

Either accept `context` as an ordinary identifier in trailing-expression
position, or — if it is genuinely a soft keyword — add it to the reserved-word
list in `.claude/rules/language.md` and make the parser say so by name.
Independently, the "expected expression, found Newline" diagnostic should carry
a line and column.

## Workaround in use

`test/01_unit/infra/counterpart/provider_registry_spec.spl` names the local
`ctx` rather than `context`.
