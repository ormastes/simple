# Test Runner Args Ci Specification

> Tests covering Test Runner Args Ci.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Args Ci Specification

## Scenarios

### Test Runner Args Ci

#### enables ci mode defaults

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- enables ci mode defaults
   - Expected: options.ci_mode is true
   - Expected: options.run_all is true
   - Expected: options.fail_fast is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables ci mode defaults")
val options = parse_test_args(["--ci"])

expect(options.ci_mode).to_equal(true)
expect(options.run_all).to_equal(true)
expect(options.fail_fast).to_equal(false)
```

</details>

#### keeps other flags when ci mode is enabled

- keeps other flags when ci mode is enabled
   - Expected: options.ci_mode is true
   - Expected: options.verbose is true
   - Expected: options.path equals `test/unit/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps other flags when ci mode is enabled")
val options = parse_test_args(["--ci", "--verbose", "test/unit/"])

expect(options.ci_mode).to_equal(true)
expect(options.verbose).to_equal(true)
expect(options.path).to_equal("test/unit/")
```

</details>

#### leaves ci mode disabled by default

- leaves ci mode disabled by default
   - Expected: options.ci_mode is false
   - Expected: options.run_all is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves ci mode disabled by default")
val options = parse_test_args([])

expect(options.ci_mode).to_equal(false)
expect(options.run_all).to_equal(false)
```

</details>

#### uses daemon-owned sequential execution by default

- uses daemon-owned sequential execution by default
   - Expected: options.session_daemon is true
   - Expected: options.session_share is true
   - Expected: options.parallel is false
   - Expected: options.sequential is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses daemon-owned sequential execution by default")
val options = parse_test_args([])

expect(options.session_daemon).to_equal(true)
expect(options.session_share).to_equal(true)
expect(options.parallel).to_equal(false)
expect(options.sequential).to_equal(true)
```

</details>

#### lets daemon child runs opt out of daemon recursion

- lets daemon child runs opt out of daemon recursion
   - Expected: options.session_daemon is false
   - Expected: options.session_share is false
   - Expected: options.parallel is false
   - Expected: options.sequential is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lets daemon child runs opt out of daemon recursion")
val options = parse_test_args(["--no-session-daemon", "--sequential"])

expect(options.session_daemon).to_equal(false)
expect(options.session_share).to_equal(false)
expect(options.parallel).to_equal(false)
expect(options.sequential).to_equal(true)
```

</details>

#### preserves sdoctest behavior

- preserves sdoctest behavior
   - Expected: options.sdoctest is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves sdoctest behavior")
val options = parse_test_args(["--sdoctest"])

expect(options.sdoctest).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/test_runner_new/test_runner_args_ci_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Test Runner Args Ci.
- Test Runner Args Ci

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `e88f050022eb4c77631d7bd97015ee002e39cd20e6130861ca4c26c184842028`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e88f050022eb4c77631d7bd97015ee002e39cd20e6130861ca4c26c184842028`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e88f050022eb4c77631d7bd97015ee002e39cd20e6130861ca4c26c184842028`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/test_runner_new/test_runner_args_ci_spec.spl
mirror: doc/06_spec/unit/app/test_runner_new/test_runner_args_ci_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/test_runner_new/test_runner_args_ci_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/test_runner_new/test_runner_args_ci_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/test_runner_new/test_runner_args_ci_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enables ci mode defaults' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/test_runner_args_ci_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps other flags when ci mode is enabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/test_runner_args_ci_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves ci mode disabled by default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
