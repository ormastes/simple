# Short Grammar Fixer Misses Casted Function Forwarding

Date: 2026-05-27

## Summary

The short-grammar fixer does not currently rewrite casted function-forwarding
callbacks of the form:

```spl
\v: callback(v as T)
```

The compiler accepts the short form:

```spl
callback(_1 as T)
```

as verified in `src/lib/nogc_sync_mut/src/future.spl`, but
`check_short_grammar_refactor` returns no fix for the long form.

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
`test/unit/app/fix/short_grammar_fix_spec.spl`.
