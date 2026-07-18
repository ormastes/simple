# Interpreter lazy import: global first use is not materialized

**Date:** 2026-07-15
**Severity:** high
**Component:** core interpreter module loader
**Status:** open

## Reproduction

```simple
# provider.spl
val answer = 73
export answer

# main.spl
use lazy provider.{answer}
print answer
```

The first read force-loads `provider`, but `answer` is still absent from the
interpreter environment and the read remains unresolved.

## Root cause

`force_deferred_module` delegates to `load_module`. That loader parses and
registers callable/type declarations through `register_module_functions`, but
does not evaluate appended `DECL_VAL`/`DECL_VAR` initializers. Consequently no
environment entry exists for `try_force_any_deferred_for` to acknowledge.

The nearby lazy-struct fix can safely register appended `DECL_STRUCT` nodes in
the existing struct table. Applying the same shape to globals would be partial
and wrong: their initializer expressions must execute exactly once with normal
module ordering and error propagation.

## Required fix

Add a cycle-safe post-load module-initialization owner shared by eager and lazy
loads. It must evaluate newly appended module declarations once, preserve
dependency order, propagate initialization errors, and publish globals only
after successful initialization. `module_loader_core` cannot directly import
`eval_decl` today because `eval_decls` already depends on the loader.
