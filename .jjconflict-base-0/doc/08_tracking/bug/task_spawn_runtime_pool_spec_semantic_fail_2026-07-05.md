# task_spawn_runtime_pool_spec.spl: semantic error — cannot assign field on non-object value

**Date:** 2026-07-05
**Area:** lib/nogc_async_mut task_spawn, interpreter semantics
**Status:** CLOSED

## Symptom

```bash
bin/simple test test/01_unit/lib/nogc_async_mut/task_spawn_runtime_pool_spec.spl --mode=interpreter --clean --timeout 60 --sequential
```

fails with:

```text
semantic: invalid assignment: cannot assign field on non-object value
```

## Context

Found during the flight-level async-evidence roll-up expansion (G5): the
task_spawn surface needed a representative passing spec for
`scripts/check/check-async-library-hardening-evidence.shs`.
`async_host_task_identity_spec.spl` (5 examples, passing) was used instead;
this spec was excluded with a comment in the checker rather than silently
dropped.

## Next Check

Reproduce, identify whether the spec assigns a field on a value-typed/copied
struct (arrays and structs are value types — see
`.claude/memory/feedback_arrays_value_types.md` pattern) or whether the
interpreter mis-types the runtime-pool object. Fix spec or interpreter at root
cause, then add this spec back to the async hardening evidence list.

## Resolution

`task_spawn` now uses the same owner-facade `rt_pool_*` boundary as
`multicore_green_spawn`: it tries `rt_pool_submit`, joins native handles through
`rt_pool_join`, and keeps the interpreter fallback inline with recorded
`TaskHandle` results. The spec was added back to
`scripts/check/check-async-library-hardening-evidence.shs`.
