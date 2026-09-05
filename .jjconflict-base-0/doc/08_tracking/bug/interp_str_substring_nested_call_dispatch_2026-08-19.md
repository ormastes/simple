# Interpreter: `substring` dispatch fails on chained str receiver with nested call argument

**Date:** 2026-08-19
**Status:** OPEN (workaround landed; root cause not fixed)
**Severity:** medium — silently breaks any spec/product path using the compact form

## Symptom

`raw_directive.trim().substring(parts[0].len()).trim()` in
`src/lib/gc_async_mut/web/browser_session_context.spl` (CSP directive parsing)
fails at runtime under the deployed seed with:

```
semantic: method 'substring' not found on value of type str in nested call context
```

This made 5 of the `browser_session_dom_input_spec.spl` form-action tests fail
(and the same class showed up as `cannot convert function to int` in
`browser_session_script_css_animation_spec.spl` chains).

## Repro

Run `bin/simple test test/02_integration/rendering/browser_session_dom_input_spec.spl`
before the workaround commit; the 5 CSP form-action examples fail with the
message above.

## Workaround

Hoisted the chain into locals (`trimmed_directive`, `head_len`) at
`browser_session_context.spl` — the semantics are identical; only the
expression shape changed. Per CLAUDE.md critical rules this compact-form
failure is recorded here rather than silently normalized.

## Next step

Reproduce in a minimal interpreter unit spec (`str.trim().substring(f())`) and
fix method dispatch on chained receivers with nested call arguments in the
interpreter call path.
