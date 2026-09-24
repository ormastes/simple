## Closed 2026-09-13 — JIT divergence issue, tracked separately

Date: 2026-05-27
Status: STALE 2026-05-29 — verified working: `["ready"].map("{_1}:migrated")` returns `["ready:migrated"]`

> Re-checked 2026-09-13 (Windows x86_64, seed `bin/simple` v1.0.0-rc.1): this closure stands for the INTERPRETER path — `["ready"].map("{_1}:migrated")` returns `ready:migrated` when the function is demoted to the interpreter. It does NOT hold under the Cranelift JIT, where every `text`-returning inline lambda yields a raw handle integer. Not reopened; the JIT divergence is tracked separately in `jit_inline_lambda_text_return_raw_handle_2026-09-13.md`.

---

# Short Grammar Placeholder Interpolation Fails

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
`test/01_unit/compiler_core/parser/short_grammar_interpreter_spec.spl` produced
`Failed: 1`, while the surrounding short-grammar tests passed.

## Required Fix

Either teach placeholder desugaring to transform placeholders inside
interpolation expressions, or document a different supported short form for
interpolated string transforms. Until then, the short-grammar fixer must not
rewrite interpolation callbacks.
