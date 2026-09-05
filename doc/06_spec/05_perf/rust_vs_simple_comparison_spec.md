# Rust Vs Simple Comparison Specification

> Tests covering Rust vs Simple Performance Comparison.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rust Vs Simple Comparison Specification

## Scenarios

### Rust vs Simple Performance Comparison

<details>
<summary>Advanced: benchmark suite runs</summary>

#### benchmark suite runs _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- benchmark suite runs
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("benchmark suite runs")
expect(1).to_equal(1)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/rust_vs_simple_comparison_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Rust vs Simple Performance Comparison.
- Rust vs Simple Performance Comparison

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1c8c9ab968755426f0ccd8af90640d6203bae5101dcad708c11874bbe8061e73`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1c8c9ab968755426f0ccd8af90640d6203bae5101dcad708c11874bbe8061e73`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1c8c9ab968755426f0ccd8af90640d6203bae5101dcad708c11874bbe8061e73`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **75/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/05_perf/rust_vs_simple_comparison_spec.spl
mirror: doc/06_spec/05_perf/rust_vs_simple_comparison_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=0
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=75; blocker cap makes effective=49
doc/06_spec/05_perf/rust_vs_simple_comparison_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/rust_vs_simple_comparison_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/rust_vs_simple_comparison_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/05_perf/rust_vs_simple_comparison_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/05_perf/rust_vs_simple_comparison_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/rust_vs_simple_comparison_spec.spl:412:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'benchmark suite runs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
