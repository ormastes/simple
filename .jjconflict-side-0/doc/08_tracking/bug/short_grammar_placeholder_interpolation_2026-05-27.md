# Short Grammar Placeholder Interpolation Fails

Date: 2026-05-27
Status: STALE 2026-05-29 — verified working: `["ready"].map("{_1}:migrated")` returns `["ready:migrated"]`

## Summary

Placeholder short grammar does not currently work inside string interpolation.
This blocks safe fixer rewrites for callbacks such as:

```spl
\x: "{x}:migrated"
```

The natural short form fails in the interpreter parser/runtime spec:

```spl
["ready"].map("{_1}:migrated")
```

Expected result:

```spl
["ready:migrated"]
```

Actual evidence: adding this case to
`test/unit/compiler_core/parser/short_grammar_interpreter_spec.spl` produced
`Failed: 1`, while the surrounding short-grammar tests passed.

## Required Fix

Either teach placeholder desugaring to transform placeholders inside
interpolation expressions, or document a different supported short form for
interpolated string transforms. Until then, the short-grammar fixer must not
rewrite interpolation callbacks.
