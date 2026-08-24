# Unsafe expression import lowering resolves `unsafe` as a function

**Status:** Seed parser/HIR fix implemented and focused-tested; deployed
imported-module execution remains pending
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

## 2026-08-24 seed parser resolution

The Rust seed parser now recognizes a colon-terminated `unsafe(...)` or
`danger(...)` header from primary-expression position, using the same
`Expr::UnsafeBlock` node as statement position. It first scans to the matching
`)` and requires the following `:`, so an ordinary expression such as
`unsafe(1)` remains an ordinary call. The shared parser consumes capability
metadata without constructing a discarded fake call expression.

Focused parser evidence passes for both the value-bound block and the ordinary
call disambiguation. Focused HIR evidence also passes and proves that the
value-bound block remains `HirExprKind::UnsafeBlock` with its `i64` tail type.
This is a parser/HIR-only change: it adds no runtime wrapper, closure,
allocation, copy, or dispatch. Rebuilding/deploying the seed and rerunning the
imported TLS fixture remain separate admission evidence.
