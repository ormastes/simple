# Interpreter: `substring` dispatch fails on chained str receiver with nested call argument
Status: SUPERSEDED. Triage 2026-11-11 (lane interp4, PR #8185): seed-smoke verified, fixing commit cited in addendum below.
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## 2026-11-10 triage — SUPERSEDED (seed-smoke, lane p3-interp4 row 22)

Fixed by 63c35af09a41 "fix(seed): dispatch slice/substring on temporary text in
nested calls" (2026-10-09, in branch): the interpreter's nested-call
dispatcher gained the Value::Str slice/substring arm — the fix message quotes
this doc's exact error ("method 'substring' not found on value of type str in
nested call context") and repro shape. Seed-smoke repro
`build/p3fix-interp4/row22_substring.spl` (the doc's
`raw_directive.trim().substring(parts[0].len()).trim()` chain): default and
SIMPLE_EXECUTION_MODE=interpreter both print `row22 result=cdef`. One
verification cycle; no fix required from this lane.
