# A Binary Override Named on the Command Line Must Reach the Spec Body

> Around 39 specs in this tree decide *which binary they exercise* from the environment — `SIMPLE_TEST_BINARY`, `SIMPLE_BINARY`, `SIMPLE_BIN`, `SIMPLE_SEED_BINARY`, `SIMPLE_SPEC_COMPILER` — in a `contract_binary()` helper that falls back to `bin/simple`. The whole point of such a spec is to be re-runnable against a *chosen* binary: a seed, a bootstrap candidate, or a deliberately sabotaged one.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# A Binary Override Named on the Command Line Must Reach the Spec Body

Around 39 specs in this tree decide *which binary they exercise* from the environment — `SIMPLE_TEST_BINARY`, `SIMPLE_BINARY`, `SIMPLE_BIN`, `SIMPLE_SEED_BINARY`, `SIMPLE_SPEC_COMPILER` — in a `contract_binary()` helper that falls back to `bin/simple`. The whole point of such a spec is to be re-runnable against a *chosen* binary: a seed, a bootstrap candidate, or a deliberately sabotaged one.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/check/test_daemon_env_override_passthrough_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Around 39 specs in this tree decide *which binary they exercise* from the
environment — `SIMPLE_TEST_BINARY`, `SIMPLE_BINARY`, `SIMPLE_BIN`,
`SIMPLE_SEED_BINARY`, `SIMPLE_SPEC_COMPILER` — in a `contract_binary()` helper
that falls back to `bin/simple`. The whole point of such a spec is to be
re-runnable against a *chosen* binary: a seed, a bootstrap candidate, or a
deliberately sabotaged one.

`bin/simple test <spec>` does not, by default, run the spec in the process you
launched. It hands the path to a long-lived helper — `src/app/test_daemon/light_daemon.spl`
— over a request file whose v1 encoding (`light_request_encode`) carries a
header, an expiry and a path, and **no environment at all**. The daemon's own
environment is whatever the invocation that first started it happened to have,
and it then outlives that invocation for minutes.

So a caller-supplied override is not merely late, it is *invisible*: the spec
body reads the daemon's stale value and exercises the wrong binary while
reporting under the name of the right one.

## Why this is a measurement bug, not a convenience bug

A dead override fails **silently and green**. Point it at a binary that does
not exist and the spec still passes, because it quietly went on testing
`bin/simple`. That is the exact shape of a sabotage control that passes for the
wrong reason: the sabotaged binary was never the one under test, so the "it
went red when I broke it, therefore the check is real" argument evaporates.

## The workaround that does not work

Resolving the override in the child shell (`"${SIMPLE_TEST_BINARY:-bin/simple}"`)
instead of via `env_get` looks like it dodges the problem. It does not. The
child shell is forked *by the daemon*, so it inherits the daemon's frozen
environment too. Measured 2026-08-02 on the Rust seed: with a daemon already
running, a spec body saw `direct=[VALUE_FIVE]` **and** `shell=[VALUE_FIVE]`
while the caller had passed `VALUE_SIX`. Both channels are asserted below for
that reason.

## Contract

Whenever any binary-override variable is set, the run takes the direct lane
instead of the daemon lane (`test_runner_client.spl`), so the value the caller
passed is the value the spec body observes — even when a daemon seeded by an
earlier, differently-configured invocation is still alive.

## Related Specifications

- test/01_unit/lib/mem_infra/guard_backend_parity_spec.spl — a sabotage control that this defect had made vacuous
- doc/08_tracking/bug/test_daemon_freezes_env_binary_override_dead_2026-08-02.md

## Scenarios

### a binary override on the command line reaches the spec body

#### delivers the override even when a daemon seeded without one is alive

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- delivers the override even when a daemon seeded without one is alive
- Seed a test daemon from an invocation that carries no override
- Run the same target again, this time naming an explicit binary override
- The spec body's own env_get must observe the value the caller passed
- A child shell forked from the spec body must observe it too


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("delivers the override even when a daemon seeded without one is alive")
step("Seed a test daemon from an invocation that carries no override")
seed_daemon_without_override()

step("Run the same target again, this time naming an explicit binary override")
val out = run_target_with("OVERRIDE_ALPHA")

step("The spec body's own env_get must observe the value the caller passed")
assert_true(observed_direct(out, "OVERRIDE_ALPHA"))

step("A child shell forked from the spec body must observe it too")
assert_true(observed_shell(out, "OVERRIDE_ALPHA"))
```

</details>

#### delivers a DIFFERENT override on the very next run rather than replaying the first

- delivers a DIFFERENT override on the very next run rather than replaying the first
- Run the target with a first override value
- Run it again with a second value, with the previous run's process still warm
- The second run must observe the second value - replaying the first is the bug
- And it must not still be carrying the first value


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("delivers a DIFFERENT override on the very next run rather than replaying the first")
step("Run the target with a first override value")
val first = run_target_with("OVERRIDE_ONE")
assert_true(observed_direct(first, "OVERRIDE_ONE"))

step("Run it again with a second value, with the previous run's process still warm")
val second = run_target_with("OVERRIDE_TWO")

step("The second run must observe the second value - replaying the first is the bug")
assert_true(observed_direct(second, "OVERRIDE_TWO"))
assert_true(observed_shell(second, "OVERRIDE_TWO"))

step("And it must not still be carrying the first value")
assert_equal(observed_direct(second, "OVERRIDE_ONE"), false)
```

</details>

#### delivers sibling selectors that name no binary variable from the original five

- delivers sibling selectors that name no binary variable from the original five
- Run the sibling-selector fixture with a first set of values
- Run it again with a second set, with the daemon from the first run still alive
- Every sibling selector must observe the second value in the Simple channel
- Replaying the first run's value is the bug this guards
- The runner must announce the bypass, naming the sibling that triggered it


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("delivers sibling selectors that name no binary variable from the original five")
step("Run the sibling-selector fixture with a first set of values")
val first = run_siblings_with("SIB_ONE")
assert_true(sibling_observed(first, "SIMPLE_MMU_DIRECT_BACKEND", "SIB_ONE"))

step("Run it again with a second set, with the daemon from the first run still alive")
val second = run_siblings_with("SIB_TWO")

step("Every sibling selector must observe the second value in the Simple channel")
assert_true(sibling_observed(second, "SIMPLE_MMU_DIRECT_BACKEND", "SIB_TWO"))
assert_true(sibling_observed(second, "LLVM_BUILD", "SIB_TWO"))
assert_true(sibling_observed(second, "T32_PYTHON_BINARY", "SIB_TWO"))
assert_true(sibling_observed(second, "SIMPLEOS_QEMU_SIMPLE_BIN", "SIB_TWO"))
assert_true(sibling_observed(second, "SIMPLE_HOSTED_BROWSER_EXECUTABLE", "SIB_TWO"))
assert_true(sibling_observed(second, "CPU_SIMD_RENDER_SCALE_TEST_SIMPLE_BIN", "SIB_TWO"))

step("Replaying the first run's value is the bug this guards")
assert_equal(sibling_observed(second, "SIMPLE_MMU_DIRECT_BACKEND", "SIB_ONE"), false)

step("The runner must announce the bypass, naming the sibling that triggered it")
assert_true(second.contains("binary-override: "))
assert_true(second.contains("SIMPLE_MMU_DIRECT_BACKEND"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TEST-DAEMON-ENV-OVERRIDE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8f7c4a37e4895023daf1bb07bb2c1770a7d2559ca4903e5fcaed3173acf4fd45`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8f7c4a37e4895023daf1bb07bb2c1770a7d2559ca4903e5fcaed3173acf4fd45`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8f7c4a37e4895023daf1bb07bb2c1770a7d2559ca4903e5fcaed3173acf4fd45`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/check/test_daemon_env_override_passthrough_spec.spl
mirror: doc/06_spec/03_system/check/test_daemon_env_override_passthrough_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/03_system/check/test_daemon_env_override_passthrough_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/test_daemon_env_override_passthrough_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/test_daemon_env_override_passthrough_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/check/test_daemon_env_override_passthrough_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'delivers the override even when a daemon seeded without one is alive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/test_daemon_env_override_passthrough_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'delivers a DIFFERENT override on the very next run rather than replaying the first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/test_daemon_env_override_passthrough_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'delivers sibling selectors that name no binary variable from the original five' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
