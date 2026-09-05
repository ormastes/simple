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
- invalid manual visibility metadata: # @manual cross-engine benchmark evidence (expected show, folded, detail, or skip)


- run the full cross-engine benchmark suite
   - Expected: fib(15) equals `610`
   - Expected: bench_for_loop() equals `19900`
   - Expected: bench_array_iterate() equals `1225`
   - Expected: (t1 >= t0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-RUST-VS-SIMPLE
step("run the full cross-engine benchmark suite")
# Real oracle: the benchmark kernels compute the values they claim to
# measure, so the suite is not just producing timing noise.
# oracle: fib(15) is the classic 610; bench_recursive_fib must match.
expect(fib(15)).to_equal(610)
# oracle: 0..200 inclusive-of-neither sum = 199*200/2 = 19900.
expect(bench_for_loop()).to_equal(19900)
# oracle: sum of 0..49 = 49*50/2 = 1225, run twice for stability.
expect(bench_array_iterate()).to_equal(1225)
# oracle: the microsecond clock never runs backwards.
val t0 = rt_time_now_unix_micros()
var spin = 0
while spin < 10000:
    spin = spin + 1
val t1 = rt_time_now_unix_micros()
expect((t1 >= t0)).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Performance |
| Status | Active |
| Source | `test/perf/rust_vs_simple_comparison_spec.spl` |
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

- `REQ-PERF-RUST-VS-SIMPLE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4958e7b267a9cf5a2991b7836e6005d6b93b700267f1e28a736e3c7d6af0f493`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4958e7b267a9cf5a2991b7836e6005d6b93b700267f1e28a736e3c7d6af0f493`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4958e7b267a9cf5a2991b7836e6005d6b93b700267f1e28a736e3c7d6af0f493`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/perf/rust_vs_simple_comparison_spec.spl
mirror: doc/06_spec/perf/rust_vs_simple_comparison_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/rust_vs_simple_comparison_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/rust_vs_simple_comparison_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/rust_vs_simple_comparison_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/rust_vs_simple_comparison_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/perf/rust_vs_simple_comparison_spec.spl:412:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'benchmark suite runs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
