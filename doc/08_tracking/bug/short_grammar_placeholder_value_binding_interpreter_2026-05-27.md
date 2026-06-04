# Short Grammar Placeholder Value Binding Fails in Interpreter Specs

**Date:** 2026-05-27
**Status:** STALE 2026-05-29 — placeholder value binding works; mock_phase3_spec failure is pre-existing me-receiver interpreter limitation, unrelated to placeholder grammar
**Area:** short grammar, interpreter, refactoring

## Summary

Placeholder short grammar checks successfully when assigned to a local value, but
the interpreter test can fail when that value is later passed as a predicate.

## Repro

In `test/01_unit/std/mock_phase3_spec.spl`, changing this supported long form:

```spl
val has_error = \call:
    call.args.len() > 0 and call.args[0] == "ERROR"
val errors = analyzer.get_calls_matching(has_error)
```

to this placeholder form:

```spl
val has_error = _1.args.len() > 0 and _1.args[0] == "ERROR"
val errors = analyzer.get_calls_matching(has_error)
```

produces:

```text
simple check test/01_unit/std/mock_phase3_spec.spl
# OK

simple test test/01_unit/std/mock_phase3_spec.spl --mode=interpreter --clean
# Failed: 1
```

## Expected

Either the placeholder expression should lower to a callable value consistently
in value-binding position, or the checker/fixer should reject this form before
runtime.

## Migration Guidance

Do not rewrite standalone local function bindings such as
`val pred = \x: x.foo()` to `val pred = _1.foo()` until interpreter support is
fixed and covered by regression tests. Rewrites remain safe in direct call
argument position where existing short-grammar parser specs cover them.
