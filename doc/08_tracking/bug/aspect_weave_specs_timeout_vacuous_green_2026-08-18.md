# Aspect weave/join-point specs time out, and the runner reports it as a vacuous green

**Date:** 2026-08-18
**Lane:** aspect dynload + startup perf
**Status:** OPEN — reproduced, not fixed
**Binary:** `/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`
(Rust seed, `59546088 2026-08-18 07:53:39.517227740 +0000`)

## Two distinct defects

### 1. `aspect_weave_spec` exhausts memory (30 GB RSS)

`bin/simple test test/01_unit/compiler/semantics/aspect_weave_spec.spl` is
killed by the resource monitor after 698s:

```
error: TIMEOUT: killed by kill_simple_monitor (rss=30055MB>=24000MB:
  .../simple run test/01_unit/compiler/semantics/aspect_weave_spec.spl).
error: test-runner: TIMEOUT: no result after 698s (unverified)
SPEC FILE VERDICT: test/01_unit/compiler/semantics/aspect_weave_spec.spl
  declared>=1 executed=1 passed=0 failed=1 dropped=0 timeout=1
  reason=child-timeout budget_ms=698000
```

30 GB for a 173-line spec is not a budget that needs raising — it is a memory
blowup. The spec drives the real source path (`parse_full_frontend` -> HIR
lowering -> `validate_aspect_contracts` -> `weave_forward_advice`), so the
blowup is somewhere in that chain, not in the spec's five examples.

`aspect_join_point_spec` fails the same way at a different budget:

```
error: test-daemon: worker killed at 204s budget: code -1
SPEC FILE VERDICT: ... executed=1 passed=0 failed=1 dropped=0 timeout=1
  reason=daemon-worker-timeout budget_ms=203007
```

### 2. The aggregate `Results:` line contradicts the per-file verdict

For the same run that recorded `failed=1 timeout=1`, the last aggregate line
printed:

```
Results: 0 total, 0 passed, 0 failed
```

A timed-out spec is reported as zero tests, which reads as a clean run and
exits 0. This is a fail-OPEN in reporting: it is exactly the "exit 0 is not a
pass" hazard the repo's own rules call out, except here even the `Results:`
line — the designated evidence — is vacuous. Any caller gating on it (CI, a
landing check, an agent) is told nothing ran rather than that something
failed.

Defect 2 is the more dangerous of the two: it hides defect 1, and it would
hide any other spec that times out.

## Not affected (same run, same binary)

```
test/01_unit/runtime/dynload_probe_spec.spl                   Results: 4 total, 4 passed, 0 failed
test/01_unit/compiler/backend/runtime_dynload_owner_source_spec.spl  Results: 2 total, 2 passed, 0 failed
test/01_unit/os/smf/dynsmf_dynload_policy_spec.spl            Results: 14 total, 14 passed, 0 failed
```

So the dynload half of the lane verifies clean; only the two aspect-weaving
specs are red.

## Related, found in the same session

`bin/simple build bootstrap` is RED at Stage 1 on this tree (unmodified,
`e9e22a1230f`) — a link failure, so stages 2 and 3 never run:

```
/usr/bin/ld: .../native-objects-YEIuhX/mod_3.o: in function
  `cli__bootstrap_main__run_rt_native_build':
simple_module:(.text.subsection+0x20d): undefined reference to `rt_native_build'
...
Stage 1 FAILED
EXIT_CODE=1
```

Hundreds of undefined references follow, dominated by `rt_unwrap_or_trap`,
`rt_is_debug_mode_enabled`, and
`compiler__mir__mir_aop_injection__inject_after_error_advice`. The driver's own
note names the cause: the selected core lane `core-c-bootstrap` is limited to
the Simple/C core ABI and these symbols sit outside it. Tracked here only
because it blocks any bootstrap-level verification of the weaver; it is not
caused by the two spec timeouts above.

## Next step

Profile the weave spec's frontend chain under a lowered RSS cap to find where
the allocation runs away, and separately make the aggregate `Results:` line
fail closed when any `SPEC FILE VERDICT` in the same run reports
`timeout=1`/`failed>=1`.

## Pre-existing test-tree divergence recorded at landing (2026-08-18)

`check-test-tree-divergence` is RED on `origin/main` BEFORE this commit:

```
FAIL — 875 diverged vs 812 baselined (64 new, 1 fixed-but-still-baselined);
  8 mirror-only (6 unallowlisted, 0 stale-allowlist)
```

The scoped-delta check confirms this commit introduces none of it:

```
check-test-tree-divergence-delta: PASS — 71 pre-existing offender(s), 0 introduced by this range
```

The full offender list is recorded verbatim beside this file, as the
step-over protocol requires, in
`aspect_weave_specs_timeout_vacuous_green_2026-08-18_divergence_offenders.txt`
(875 lines). It is data, not prose, so it is kept out of this document rather
than pasted into it.

## 2026-08-18 (later, lane-aspect-dynload): PREMISE NO LONGER HOLDS — the
## 30 GB blowup does not reproduce; both specs now fail in ~2 min for an
## unrelated, non-aspect reason

Binary at the time of this re-measurement (the shared seed was REDEPLOYED
between the two measurements — this is a different binary from the one the
original report used):

```
$ readlink -f bin/simple
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
$ stat -c '%s %y' "$(readlink -f bin/simple)"
59645008 2026-08-18 10:12:23.164167908 +0000     # report used 59546088 @ 07:53:39
```

Re-run of the exact command the kill message named, detached, RSS polled from
`/proc/PID/status` every 10s: peak VmRSS **3932 kB**, finished in ~110s. No
timeout, no memory growth:

```
$ bin/simple run test/01_unit/compiler/semantics/aspect_weave_spec.spl
  semantic: undefined field 'level': cannot access field on value of type 'object'   (x5)
5 examples, 5 failures
SPEC FILE VERDICT: test/01_unit/compiler/semantics/aspect_weave_spec.spl outcome=OK declared>=5 executed=5 passed=0 failed=5 skipped=0 dropped=0

$ bin/simple run test/01_unit/compiler/semantics/aspect_join_point_spec.spl
  semantic: undefined field 'level': cannot access field on value of type 'object'   (x10)
10 examples, 10 failures
SPEC FILE VERDICT: .../aspect_join_point_spec.spl outcome=OK declared>=10 executed=10 passed=0 failed=10 skipped=0 dropped=0
```

Both are now red for the SAME cause, and it is not in the aspect code at all.
The failing access is `frontend.spl:26` (`fn frontend_log_trace(log: Logger,
...)` -> `if log.level >= 20:`), reached from `parse_full_frontend` — but the
defect is upstream of even that. Minimal reproduction, 12 lines, importing
NOTHING from `35.semantics`, `10.frontend/aspect_registry.spl`, or the weaver:

```simple
use std.spec.{describe, it, expect}
use compiler.common.config.{Logger}

fn probe_local(log: Logger) -> i64:
    if log.level >= 20: 1 else: 0

describe "logger probe":
    it "reads level locally":
        expect(probe_local(Logger(level: 0))).to_equal(0)
    it "reads level directly":
        val l = Logger(level: 3)
        expect(l.level).to_equal(3)
```

Result: `2 examples, 2 failures`, both `undefined field 'level': cannot access
field on value of type 'object'`. So a `class` instance (`Logger`,
`src/compiler/00.common/config.spl:171`) constructed from an importing module
is erased to a plain `object` by the current seed, and EVERY field read on it
fails — including a direct `val l = Logger(level: 3); l.level`. Nothing about
aspects, weaving, join-point enumeration, or the weave loop's `modules[
module_key] = module` value-copy is involved.

Consequences for the original report:
* Defect 1 (30 GB in `weave_forward_advice`) is **not reproducible on the
  current binary** and its suspected causes (unbounded weave loop, non-
  terminating re-enumeration, failed idempotence guard) are unverified — the
  specs never reach `weave_forward_advice` now; they die in `parse_full_frontend`.
  Do not "fix" the weaver against this report without first re-reproducing on a
  named binary.
* Defect 2 (vacuous `Results: 0 total`) is untouched by this and still stands.
* The blocking work is now the class-field erasure above, which belongs to the
  seed/interpreter owners, not to the aspect lane.
