# `wm_action_applier_spec` executes NOTHING on both legs — `vulkan_order_env_get` not found

**Status:** PRIMARY DEFECT RESOLVED 2026-08-17 — the spec now EXECUTES (17/17,
14 passed). Three genuine failures it was hiding are now visible and remain
open; see the re-verification section. Still: do not delete or skip the spec.
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


## 2026-08-17 re-verification — the spec is no longer dead

The `zero-examples` cause is fixed. `vulkan_order_env_get` no longer exists as a
dangling reference: `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl`
dropped the `use ... {env_get as vulkan_order_env_get}` aliased import and now
carries a NOTE at lines 10-13 recording exactly why the alias must not come back
(it resolved to nothing and killed the whole spec file with `error[E1002]`).

Measured now, numbered leg:

```
SPEC FILE VERDICT: test/01_unit/os/compositor/wm_action_applier_spec.spl declared>=17 executed=17 passed=14 failed=3 dropped=0
Results: 17 total, 14 passed, 3 failed
```

`executed=17` where it was `executed=0 dropped=1 reason=zero-examples`. All 17
`it` blocks are live, so the `@cover src/os/compositor/wm_action_applier.spl 80%`
claim is now backed by real execution rather than by nothing.

### The three failures this was hiding — now open on their own merits

Two are stale-spec / API drift, one looks like a real behavioural defect:

1. `materializes shared GUI WindowManager state into SimpleOS compositor surfaces`
   — `semantic: class WindowSurface has no field named session`. Spec references
   a field the class no longer has; needs repointing at the current API (or the
   field restoring, if its removal was the regression).
2. `creates web windows with a Simple Web render request surface`
   — `semantic: function wm_action_web_window_request not found`. Same class of
   drift, at function granularity.
3. `moves and resizes lifecycle windows from host-neutral pointer state`
   — `expected subject to be truthy, got 0`. This one is NOT a missing symbol:
   it type-checks, runs, and returns the wrong value. **Most likely a real
   product defect in move/resize handling** and the highest-value follow-up here.

These were deliberately NOT patched in this pass: (1) and (2) must be resolved
against the current API by someone who can confirm which side moved (spec vs.
source), and silently repointing them risks weakening assertions the way the
original `match`-on-single-variant problem did elsewhere; (3) needs its own
root-cause investigation and its own repro + generalization specs. Do not soften
any of the three into `pending`.

**Not re-measured:** the legacy `test/unit/os/compositor/wm_action_applier_spec.spl`
leg (12 `it` blocks) — it should be run and reconciled with the numbered leg,
since the two trees diverged and this record covers both.
