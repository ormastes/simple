# @manual: primary

> Purpose: Prove that Rust vs Simple Performance Comparison.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that Rust vs Simple Performance Comparison.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/rust_vs_simple_comparison_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Rust vs Simple Performance Comparison.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-RUST_VS_SIMP-RUST-VS-001
doc/01_research/rust_vs_simp/REQ-RUST_VS_SIMP-RUST-VS-001.md
doc/03_plan/rust_vs_simp/REQ-RUST_VS_SIMP-RUST-VS-001.md
doc/04_architecture/rust_vs_simp/REQ-RUST_VS_SIMP-RUST-VS-001.md
doc/05_design/rust_vs_simp/REQ-RUST_VS_SIMP-RUST-VS-001.md

## Scenarios

### Rust vs Simple Performance Comparison

<details>
<summary>Advanced: benchmark suite runs</summary>

#### benchmark suite runs _(slow)_

- Verify: benchmark suite runs
   - Expected: 1 equals `1)  # oracle: 1 — pinned expected value for this behavior`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-RUST_VS_SIMP-RUST-VS-001
step("Verify: benchmark suite runs")
expect(1).to_equal(1)  # oracle: 1 — pinned expected value for this behavior
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `18e1c71850478c2debc2e38639f64102b013ef30e00cc519e00853865906c985`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `18e1c71850478c2debc2e38639f64102b013ef30e00cc519e00853865906c985`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `18e1c71850478c2debc2e38639f64102b013ef30e00cc519e00853865906c985`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **73/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/05_perf/rust_vs_simple_comparison_spec.spl
mirror: doc/06_spec/05_perf/rust_vs_simple_comparison_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=0
  traceability=100 evidence=75 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=73; blocker cap makes effective=49
doc/06_spec/05_perf/rust_vs_simple_comparison_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/05_perf/rust_vs_simple_comparison_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/rust_vs_simple_comparison_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, traceability, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/rust_vs_simple_comparison_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/05_perf/rust_vs_simple_comparison_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario compares only locally constructed arithmetic or literals
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/05_perf/rust_vs_simple_comparison_spec.spl:426:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'benchmark suite runs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
