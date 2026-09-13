## Closed 2026-09-13 — prior in-body resolution, carried forward (NOT re-verified this pass)

Reviewed in the 2026-05-and-earlier bug/todo tracking sweep. This entry already
recorded its own resolution before this pass; the header exists so the closure is
visible at the top rather than buried in the body. First status line found:

> Status: Resolved

This is a closure marker, not a new claim: the repro was **not** re-run in this
sweep. The original evidence in the body stands on its own. Re-open with a fresh
dated repro if the symptom returns — do not treat this header as verification.

---

# Short Grammar Fixer Misses Casted Function Forwarding

Date: 2026-05-27
Status: Resolved

## Summary

The short-grammar fixer previously missed casted function-forwarding callbacks
of the form:

```spl
\v: callback(v as T)
```

The compiler accepts the short form:

```spl
callback(_1 as T)
```

as verified in `src/lib/nogc_sync_mut/src/future.spl`, but
`check_short_grammar_refactor` returned no fix for the long form.

Resolved by the regression `rewrites casted function forwarding calls` in
`test/01_unit/app/fix/short_grammar_fix_spec.spl`.

## Expected

The fixer should rewrite safe captured function calls with a casted callback
argument:

```spl
\v: callback(v as i64)
```

to:

```spl
callback(_1 as i64)
```

## Notes

Receiver call forwarding with casted arguments is already covered by
`rewrites casted receiver forwarding calls` in
`test/01_unit/app/fix/short_grammar_fix_spec.spl`.
