# task_spawn_runtime_pool_spec.spl: semantic error — cannot assign field on non-object value

**Date:** 2026-07-05
**Area:** lib/nogc_async_mut task_spawn, interpreter semantics
**Status:** RESOLVED (2026-09-12, re-verified: spec now passes)

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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule B: cheap repro run against the deployed seed); the exact repro command from the record now passes. Evidence: `bin/simple test test/01_unit/lib/nogc_async_mut/task_spawn_runtime_pool_spec.spl --mode=interpreter --clean --timeout 60 --sequential` on deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) -> `1 total, 1 passed, 0 failed`.
