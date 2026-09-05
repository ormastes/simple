# Test Runner Daemon Readiness Specification

> Tests covering test runner daemon readiness.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Runner Daemon Readiness Specification

## Scenarios

### test runner daemon readiness

#### requires a responsive daemon at both routing gates

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires a responsive daemon at both routing gates
   - Expected: source.split("test_daemon_ensure_responsive(daemon_config)").len() equals `3`
   - Expected: source does not contain `test_daemon_ensure_running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("requires a responsive daemon at both routing gates")
val source = rt_file_read_text("src/app/test_runner_new/test_runner_main.spl") ?? ""

expect(source.split("test_daemon_ensure_responsive(daemon_config)").len()).to_equal(3)
expect(source.contains("test_daemon_ensure_running")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/test_runner_daemon_readiness_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering test runner daemon readiness.
- test runner daemon readiness

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ccf5944a0d3f21cf263ab223190932bf28868321dc01dfd522d3d992952c3b98`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ccf5944a0d3f21cf263ab223190932bf28868321dc01dfd522d3d992952c3b98`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ccf5944a0d3f21cf263ab223190932bf28868321dc01dfd522d3d992952c3b98`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **77/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/test_runner_new/test_runner_daemon_readiness_spec.spl
mirror: doc/06_spec/01_unit/app/test_runner_new/test_runner_daemon_readiness_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=40
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=77; blocker cap makes effective=49
doc/06_spec/01_unit/app/test_runner_new/test_runner_daemon_readiness_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/test_runner_new/test_runner_daemon_readiness_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/test_runner_new/test_runner_daemon_readiness_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/test_runner_new/test_runner_daemon_readiness_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/test_runner_new/test_runner_daemon_readiness_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/test_runner_new/test_runner_daemon_readiness_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires a responsive daemon at both routing gates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
