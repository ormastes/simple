# `native-build` exit 0 must imply the artifact contains a function

> A `native-build` was observed emitting an 11 KB ELF whose symbol table held 294 `FILE` symbols and **zero `FUNC` symbols**, while the lane printed `Build complete` and exited 0. A binary with no defined function has no `main`/`_start` body; it cannot be a successful build.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `native-build` exit 0 must imply the artifact contains a function

A `native-build` was observed emitting an 11 KB ELF whose symbol table held 294 `FILE` symbols and **zero `FUNC` symbols**, while the lane printed `Build complete` and exited 0. A binary with no defined function has no `main`/`_start` body; it cannot be a successful build.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Driver / native-build — vacuous success (similar-problem detection) |
| Status | Active |
| Source | `test/01_unit/compiler/driver/native_build_success_implies_functions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

A `native-build` was observed emitting an 11 KB ELF whose symbol table held
294 `FILE` symbols and **zero `FUNC` symbols**, while the lane printed
`Build complete` and exited 0. A binary with no defined function has no
`main`/`_start` body; it cannot be a successful build.

This is the same defect class as `TestRunResult::success()` being
`total_failed == 0` — a process reporting success while its own accounting
says it produced nothing. It is dangerous in proportion to how much is
downstream of it: many lanes use the `native-build` exit code as their sole
oracle, inspecting no symbols and executing no result.

## What this spec pins

Not one observed artifact, but the INVARIANT the observation violated:

    native-build exit 0  ==>  the emitted artifact defines >= 1 FUNC symbol

asserted across several program shapes, so a fix that special-cases the one
reported shape does not satisfy it. The shapes differ in what could plausibly
make codegen emit nothing:

| shape | why it is a distinct member |
|---|---|
| `main` only | the minimum a program can be |
| `main` + a called helper | a second body that must also survive |
| `main` + an UNCALLED helper | dead code must not take live code with it |

The negative half — that a genuinely functionless artifact is REJECTED — is
covered by `scripts/check/check-native-build-artifact-has-functions.shs`,
whose own fatal `--selftest` assembles a real 0-`FUNC` ELF and requires it to
be rejected. This spec invokes that selftest so the two cannot drift apart:
a spec that only ever sees good builds would pass with the gate deleted.

## Why this MUST run in a SUBPROCESS

`native-build` is a codegen + link path. A spec body runs INTERPRETED and
never reaches it, so an in-process example could not go red no matter how
broken the driver is. Every measurement here is taken by shelling out and
reading `readelf -sW` on the artifact the build actually produced. Exit codes
are captured with `echo RC=$?` immediately after the command — never through a
pipe, whose status belongs to its last stage.

## Scenarios

### a native-build that exits 0 has emitted at least one function

#### produces an artifact with real function bodies for a normal program

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces an artifact with real function bodies for a normal program
- Build a program with a live helper, a called path, and dead code
- Refuse to pass on a run that produced no census line at all
- The build reported success
- An artifact exists — the existence check the old funnel had
- And it is NOT functionless — the check the old funnel did not have
   - Expected: census does not contain `FUNC=0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces an artifact with real function bodies for a normal program")
# Deliberately ONE example over a three-function program: each
# `native_build_and_census()` costs a full native-build, and spec module
# globals do not persist across examples, so three examples would mean
# three builds for no extra coverage.
step("Build a program with a live helper, a called path, and dead code")
val census = build_and_census()

step("Refuse to pass on a run that produced no census line at all")
expect(census).to_contain("RC=")
expect(census).to_contain("FUNC=")

step("The build reported success")
expect(census).to_contain("RC=0")

step("An artifact exists — the existence check the old funnel had")
expect(census).to_contain("EXISTS=1")

step("And it is NOT functionless — the check the old funnel did not have")
# This is the whole point: `EXISTS=1` was already enforced at
# compile_targets.spl:1239 and is satisfied by an 11 KB ELF with 294
# FILE symbols and 0 FUNC symbols. Only the line below rejects that.
expect(census.contains("FUNC=0")).to_equal(false)
```

</details>

#### keeps the functionless-artifact gate's own negative control alive

- keeps the functionless-artifact gate's own negative control alive
- Run the gate's fatal selftest, which assembles a real 0-FUNC ELF
- It must both PASS and say it rejected the 0-FUNC control


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the functionless-artifact gate's own negative control alive")
step("Run the gate's fatal selftest, which assembles a real 0-FUNC ELF")
val out = process_run("sh", ["-c",
    "sh scripts/check/check-native-build-artifact-has-functions.shs " +
    "--selftest 2>&1; echo RC=$?"])
step("It must both PASS and say it rejected the 0-FUNC control")
# Asserting only `RC=0` would pass if the selftest were gutted to a
# `true`; asserting the control text keeps the negative control real.
expect(out.0).to_contain("RC=0")
expect(out.0).to_contain("0-FUNC rejected")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `75a00200d0d3dafc4a216f3b7ffa59cd1f36712f471fe9b2429d1012bc259276`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `75a00200d0d3dafc4a216f3b7ffa59cd1f36712f471fe9b2429d1012bc259276`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `75a00200d0d3dafc4a216f3b7ffa59cd1f36712f471fe9b2429d1012bc259276`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/compiler/driver/native_build_success_implies_functions_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/native_build_success_implies_functions_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/native_build_success_implies_functions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/native_build_success_implies_functions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/native_build_success_implies_functions_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces an artifact with real function bodies for a normal program' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/native_build_success_implies_functions_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the functionless-artifact gate's own negative control alive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
