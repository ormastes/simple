# `wm_action_applier_spec` executes NOTHING on both legs — `vulkan_order_env_get` not found

**Status:** OPEN — RED and left RED. Do not delete or skip the spec.
**Filed:** 2026-08-10
**Found by:** repairing the half-landed fix on `os/compositor/wm_action_applier_spec.spl`
(`doc/08_tracking/test/half_landed_fixes_across_duplicate_test_trees_2026-08-10.md`).

## Symptom

Both executing legs report:

```
SPEC FILE VERDICT: test/01_unit/os/compositor/wm_action_applier_spec.spl declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=zero-examples
SPEC FILE VERDICT: test/unit/os/compositor/wm_action_applier_spec.spl     declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=zero-examples
```

with, earlier in the log:

```
error[E1002]: function `vulkan_order_env_get` not found
error: test-runner: no examples executed
```

## Scope

This is **pre-existing and independent of the tree divergence** — verified by
running the unmodified committed content of BOTH legs at the origin base: both
already reported `zero-examples`. The numbered leg's 17 `it` blocks and the
legacy leg's 12 have therefore all been dead. `@cover
src/os/compositor/wm_action_applier.spl 80%` is being claimed by a spec that
runs no examples at all.

`vulkan_order_env_get` is reached transitively through
`os.compositor.compositor`, so every spec importing `Compositor` is a candidate
for the same failure; this file is only the instance that surfaced.

## Unblock condition

Resolve `vulkan_order_env_get` (declare/export it, or drop the dead reference
from the `os.compositor.compositor` import chain). Then both legs should execute
18 examples.

## Do not

Do not "fix" this by deleting `it` blocks, removing the `Compositor` import, or
marking the file pending. A spec that reports `zero-examples` is a defect
report, not a spec to be quietened.
