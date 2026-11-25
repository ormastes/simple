# Interpreter lazy import: global first use is not materialized
## Resolved — fix present in source (verified by inspection 2026-11-25)

**Date:** 2026-07-15
**Severity:** high
**Component:** core interpreter module loader
**Status:** resolved (see 2026-11-25 section below)

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


## Resolution verified 2026-11-25 — both required pieces are in the tree

The 2026-09-16 normalization pass found no resolution evidence because it
reviewed this record, not the source. The "Required fix" above has since
landed in `src/compiler/10.frontend/core/interpreter/module_loader_core.spl`:

1. **Module initialization pass** — `load_module` (around line 616) now
   evaluates newly appended `DECL_VAL`/`DECL_VAR` (and `DECL_ENUM`/`DECL_IMPL`/
   `DECL_CLI`) initializers via `eval_decl` after the dependency graph is
   registered, exactly once, with error propagation (`eval_had_error` aborts
   the load) and dependency order preserved by the preceding dependency loop.
   The in-code comment states the rationale ("Imported modules own their
   global declarations... initialize those owners once the dependency graph
   is registered").
2. **Global acknowledgement on first use** — `try_force_any_deferred_for`
   (around line 179) now checks `env_lookup(symbol_name)` in addition to the
   function/struct tables after force-loading, so a lazy import whose first
   use is a module-global read is reported resolved. The in-code comment
   cites this bug record by filename.

Verification limit: the fixed code is the pure-Simple interpreter, which can
only be exercised through a self-hosted build; on this Windows host the
pinned binary is the Rust seed (v1.0.0-rc.1) and `bin/simple.exe test` fails
repo-wide at release/1.0.0 HEAD (`unknown decorator
'@representation_boundary'` — source/binary inconsistency), so this is
verified by code inspection, not by executing the pure-Simple lane. The
entry's repro shape (`use lazy provider.{answer}` / first read of `answer`)
prints `73` on the seed's own interpreter, consistent but not probative for
the pure-Simple lane.
