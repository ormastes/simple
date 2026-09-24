# `SIMPLE_PERF_SELF_BIN` is served from the test daemon's frozen environment
## Closed 2026-09-16 — primary defect RESOLVED 2026-09-13, fix pinned by 3 guard rows (separate SIMPLE_BINARY hole noted)

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

- Status: RESOLVED (2026-09-13) — diagnosed by PERF-7 (the measured repro and
  cause below are theirs); the one-line fix applied and pinned by PERF-9.
- Found by: PERF-7, re-running a perf parity spec against the BASE seed after
  having run it against the CANDIDATE seed.
- Extends `perf_spec_binary_resolution_falls_through_to_deployed_seed_2026-09-13.md`
  (PERF-6), which covered the directory-mode case. This is the single-file case,
  and it is worse: the binary is not merely defaulted, it is silently taken from
  a PREVIOUS run.

## Repro (measured)

Three single-file invocations of the same spec, in order:

```
SIMPLE_PERF_SELF_BIN=<BASE>  bin/simple test test/05_perf/interp/owned_method_call_parity_spec.spl
    -> [perf] binary=<BASE>   outcome=ERROR passed=2 failed=7      (correct)
SIMPLE_PERF_SELF_BIN=<CAND>  bin/simple test ...same spec...
    -> [perf] binary=<CAND>   outcome=OK     passed=10 failed=0    (correct)
SIMPLE_PERF_SELF_BIN=<BASE>  bin/simple test ...same spec...
    -> [perf] binary=<CAND>   outcome=OK     passed=10 failed=0    (WRONG)
```

The third run asked for the base seed and exercised the candidate. Its verdict is
indistinguishable from a genuine result: 10/10 green, no warning, no diagnostic.
The only thing that betrayed it was the `[perf] binary=` line the spec prints —
which exists solely because PERF-6 was bitten by the sibling defect.

## Cause

`test_runner_client.spl` diverts a request past the light daemon whenever the
caller sets one of a closed list of environment overrides — `_has_binary_override()`
(`SIMPLE_TEST_BINARY` and friends), `SIMPLE_COVERAGE`, `SIMPLE_REQUIRE_GPU`, the
`test_env_gate` family. The daemon is a long-lived process whose environment is
frozen at whichever invocation started it, and the v1 request carries a header,
an expiry and a path — **no environment at all**. The file says so itself, at
length, at lines 709-735.

`SIMPLE_PERF_SELF_BIN` is not on that list. It is, however, exactly the same kind
of variable: it names WHICH BINARY THE SPEC EXERCISES. So a daemon-served run
resolves it from the daemon's stale copy. Whether a given run is correct depends
on whether it happened to start the daemon: the first run above did (daemon
absent), the second did (the first daemon had expired), the third did not.

## Fix (applied by PERF-9)

`SIMPLE_PERF_SELF_BIN` appended to `_binary_override_vars()` in
`src/app/test_runner_new/test_runner_client.spl` — the existing fail-safe divert
for precisely this defect class, so no new mechanism. `_has_binary_override()`
reads that list, `binary_override_bypass` is one of the seven conditions that
force `daemon_ok = false`, and the `not daemon_ok` branch then prints
`binary-override: SIMPLE_PERF_SELF_BIN set; bypassing test daemon so the
override reaches the spec`.

Pinned by three `PERFSELFBIN` rows in
`scripts/check/check-perf-regression-tests.shs`: the name is in the list, the
list is still what the override check reads, and a named override still forces
the divert. Those three fail if any link is removed.

The residual gap that list cannot close is already documented above: a daemon
started WITH the variable set keeps serving it to later runs that do not set it,
because the request carries no environment. The real fix remains putting the
caller's environment in the request.

`SIMPLE_PERF_COUNTERS`, `SIMPLE_PERF_COUNTERS_OUT` and `SIMPLE_ENV_AUDIT` have
the same freeze exposure and are deliberately NOT added to this list: they are
not binary selectors, so putting them there would be a category error.

### One thing PERF-9 could not reproduce, stated rather than papered over

PERF-9 did not re-derive PERF-7's red-to-green transition locally. Every probe
run in that lane hit the `invoker_bypass` that sits ahead of the binary-override
check in the same chain (`test daemon identity is unavailable or mismatched;
bypassing daemon`), because no daemon started by the same binary was live. The
evidence for the fix is therefore PERF-7's measured repro above plus the code
path, not a second local transition. A probe spec that brings a daemon up
deliberately — the shape of
`test/01_unit/lib/common/test_env_gate/p14_env_propagation_probe_spec.spl` —
would close that, and is the named next step.

## Meanwhile

Every perf spec that resolves a binary must print `[perf] binary=<path>` as its
first line in every scenario, and any lane comparing two seeds must read that
line rather than trusting the verdict. PERF-7 re-ran its RED leg after confirming
no daemon was live (`ps -eo pid,args | grep light_daemon` empty); its receipt
records both the wrong run and the corrected one rather than only the corrected
one.

## A SECOND, separate hole in the same area (PERF-9, 2026-09-13) — still OPEN

`SIMPLE_BINARY=<any binary> bin/simple test <spec>` does not merely fail to
divert — it produces WRONG VERDICTS. Measured at `origin/main` `6ff00b3df42`
plus this lane's commits, on `test/01_unit/interpreter/`:

```
<candidate> test test/01_unit/interpreter/                     -> 3 specs OK, 17/17
SIMPLE_BINARY=<candidate> bin/simple test  ...same dir...      -> 3 specs ERROR, 3/17
SIMPLE_BINARY=<deployed seed> bin/simple test <one spec>       -> ERROR 0/3
```

The third line is the control that settles it: the named binary is the
**deployed seed itself**, the very binary that passes that spec 3/3 when it runs
the spec directly. So the route is broken for ANY binary, is not caused by the
binary named, and is not caused by adding `SIMPLE_PERF_SELF_BIN` to the override
list (the failing specs — `chained_call_*` — are untouched by that change and
fail with the override pointed at the deployed seed too).

Consequence for every lane: **`<candidate> test <path>`, invoking the seed
directly as the runner, is the only trustworthy way to point a suite at a
private build.** A `SIMPLE_BINARY=` run is not a weaker measurement, it is a
false RED.

