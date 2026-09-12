# macOS arm64: `simple test` child produces no exit status — spawn/reap failure at the process layer

- **Status:** OPEN (filed 2026-09-12)
- **Severity:** P1 — `simple test` cannot execute ANY spec on this host
- **Lane:** macOS open-bugs round 2, LANE 3. Found while fixing
  `test_runner_reports_early_child_death_as_outer_bound_timeout_2026-09-12.md`,
  which was the MISREPORTING of this defect. That one is resolved; this is the
  underlying fault and it is untouched.
- **Host:** macOS 25.5.0, Apple M4
- **Binary:** `/Users/ormastes/simple/build/cargo-r2/release/simple`
  (`stat -f '%z %m'` = `39528776 1789199850`) — a CURRENT seed, not the stale
  Jul-25 full CLI. This is NOT the stale-deploy-slot defect.

## Reproduce (exact command, any spec — the spec is irrelevant)

```
timeout 120 /Users/ormastes/simple/build/cargo-r2/release/simple test \
  --no-session-daemon --timeout 900 \
  test/01_unit/lib/common/spec/exists_check_assertion_generalization_spec.spl
```

```
inner_rc=5
Results: 0 total, 0 passed, 0 failed
Duration: 3ms
UNVERIFIED <spec>: TERMINATED: child produced no exit status -- spawn or reap
  failure at the process layer, not a timeout and not a signal death (unverified)
```

The same spec run through `run` instead of `test` passes 4/4, so neither the
spec nor the compiler is at fault:

```
SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0 <seed> run <spec>
  -> 4 examples, 0 failures
```

## What is known

- **3ms, every time.** Nothing is executed; the failure is at spawn/reap, before
  any spec code runs.
- **The inner single-runner already classifies it correctly** — it says in so
  many words "not a timeout and not a signal death". The diagnosis was present
  in the tree the whole time; only the outer client
  (`test_runner_new/test_runner_client.spl`, `run_one_direct`) discarded it and
  reported `reason=outer-bound-timeout budget_ms=930000`. That laundering is
  what hid this defect, and is now fixed — hence this record exists at all.
- **Not the stale deploy slot.** `macos_test_runner_blocked_inline_unsafe_and_wrong_deploy_slot_2026-08-31.md`
  describes `bin/simple` resolving to a bootstrap CLI in the stage-4 full-CLI
  slot. This reproduction bypasses `bin/simple` entirely and invokes a current
  seed by absolute path, so that record does not explain it. The two are
  related only in that both block `simple test` on this host.

## Not yet investigated

The process layer itself — `app.io.process_ops.process_run_bounded` and the
`rt_process_*` backing it on Darwin. "No exit status" points at a `waitpid`
/ `posix_spawn` path returning something the wrapper cannot map, plausibly a
macOS-specific gap in the reap loop. Nobody has read that code for this symptom
yet; this record deliberately stops at the measurement rather than guessing.

## Unblock condition

`simple test <any spec>` executes the spec's examples and reports a real
verdict, matching what `simple run <same spec>` reports.

## Impact

Every lane oracle phrased as "`simple test` and `simple run` agree" is
unreachable on macOS arm64 until this is fixed. Lane 3's oracle is in that
shape and is therefore NOT met: the disagreement is now honestly reported
rather than resolved.
