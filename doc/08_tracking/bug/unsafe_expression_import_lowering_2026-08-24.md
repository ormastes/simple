# Unsafe expression import lowering resolves `unsafe` as a function

**Status:** Open
**Observed:** 2026-08-24
**Area:** frontend/import lowering and lexical unsafe expressions

## Reproduction

An imported module containing:

```simple
val value = unsafe(capabilities: [ffi]):
    rt_env_get("KEY")
```

is accepted by source-only tooling, but executing a caller that imports and
invokes the containing function fails with:

```text
semantic: function `unsafe` not found
```

The statement/block form parses and executes:

```simple
var value = ""
unsafe(capabilities: [ffi]):
    value = rt_env_get("KEY")
```

## Required resolution

Lower expression-form unsafe through the same lexical capability HIR node as
the block form. It must preserve the inner expression type and value, reject
missing capabilities identically in every compiler stage, and introduce no
closure, allocation, dynamic dispatch, or runtime wrapper. Add an executed
imported-module fixture; source-shape acceptance alone is insufficient.

## 2026-08-24 TLS transcript reproduction

`src/os/tls13/transcript.spl` now uses value-bound lexical unsafe blocks for
the hosted SHA-256 accelerator. The focused `_finished_probe_spec.spl` reaches
the imported module and fails two transcript-dependent examples with the same
`semantic: function unsafe not found` diagnostic; the unrelated finished-key
example passes. This confirms the defect on a security-critical imported
module rather than only a synthetic environment-read reproducer.

The source is intentionally not rewritten to an extra helper-call workaround:
lexical unsafe must lower as a zero-runtime-cost HIR marker. Fixing the compiler
remains required for authoritative execution of the hardened transcript path.
