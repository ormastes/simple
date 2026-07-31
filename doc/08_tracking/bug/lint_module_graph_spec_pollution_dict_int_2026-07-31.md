# Specs importing compiler.tools.lint.main gain a file-level failure: "cannot convert dict to int"

**Date:** 2026-07-31
**Severity:** spec-verdict pollution — example results stay correct, but every
affected spec FILE reports one extra failure
**Status:** open (defect is in a dependency, not in the lint specs)

## Symptom

Any spec that imports `compiler.tools.lint.main` (which pulls the whole
compiler module graph) now ends with:

```
error: semantic: type mismatch: cannot convert dict to int
error: test-runner: spec failed
```

after all its examples pass. Both lint specs show it identically:

- `test/01_unit/compiler/lint/collection_easy_fix_spec.spl` — 3/3 examples
  green at push time (`9feda786614a`), now `4 total, 3 passed, 1 failed`.
- `test/01_unit/compiler/lint/collection_index_mutation_spec.spl` — 6/6
  examples green, `7 total, 6 passed, 1 failed`.

The +1 is the file-level entry, not an example. A green-example/red-file
verdict means CI on these files reads as failing while the code under test is
fine.

## Attribution (partial)

The same error string was traced earlier the same day to
`src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:305,312` while
that file was another session's uncommitted WIP; it has since landed and the
working copy matches origin. The types at those lines look consistent
(`val STATICS_FAILED_KEY: i64 = -1`, `handles: Dict<i64, i64>`), and the
file's own :262 comment references a known "interpreter bug as
STATICS_FAILED_KEY above" — so this is likely the interpreter mis-typing a
module-level annotated `val` used as a dict key, not a genuine source error.
`bin/simple check` on the adapter exceeds 300 s (whole-graph check), so exact
attribution is unconfirmed.

## Impact

Any spec whose module graph includes the compiler backend cannot produce a
clean file verdict until this is fixed. The examples themselves still execute
and score.

## Probe result (negative)

The minimal shape does NOT reproduce: a spec with module-level
`val K: i64 = -1` and `handles: Dict<i64, i64>; handles[K] = 1` inside a fn
passes 1/1 with no semantic error. So the trigger is not simply an annotated
module-level `val` used as a dict key — it needs more of the adapter's context
(or lives in a different file altogether; the error line names no file).
Attribution remains unconfirmed. Next candidate probe: bisect by importing
successively larger slices of `compiler.tools.lint.main`'s dependency graph
from a one-example spec until the file-level error appears.
