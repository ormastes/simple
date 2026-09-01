# Sspec Documentization Maintenance Perf Specification

> Tests covering SSpec documentization maintenance performance.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sspec Documentization Maintenance Perf Specification

## Scenarios

### SSpec documentization maintenance performance

#### scans one thousand representative pairs within the selected bound

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-001
```

</details>

#### keeps warm representative p95 below five hundred milliseconds

- keeps warm representative p95 below five hundred milliseconds
   - Expected: score equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("keeps warm representative p95 below five hundred milliseconds")
val source = representative_source()
val manual = representative_manual(sha256_text(source))
var samples_us: [i64] = []
var i: i64 = 0
while i < 20:
    val started = time_now_unix_micros()
    val score = analyze_sspec_pair_text(
        "test/warm_fixture_spec.spl", source, Some(manual)).score.aggregate
    val elapsed = time_now_unix_micros() - started
    samples_us.push(elapsed)
    expect(score).to_equal(100)
    i = i + 1
samples_us.sort()
# Nearest-rank p95 for twenty retained warm samples: ceil(20 * .95) - 1.
expect(samples_us[18]).to_be_less_than(500001)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/05_perf/app/sspec_documentization_maintenance_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SSpec documentization maintenance performance.
- SSpec documentization maintenance performance

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

- `REQ-SSPEC-PERF`
- `REQ-001\n`
- `REQ-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6c04d377fb76b411ece018ffded56f366996cb7543065006c02716cf9173b0e3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6c04d377fb76b411ece018ffded56f366996cb7543065006c02716cf9173b0e3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6c04d377fb76b411ece018ffded56f366996cb7543065006c02716cf9173b0e3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/05_perf/app/sspec_documentization_maintenance_perf_spec.spl
mirror: doc/06_spec/05_perf/app/sspec_documentization_maintenance_perf_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=90
  traceability=100 evidence=90 coverage=80 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/app/sspec_documentization_maintenance_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/app/sspec_documentization_maintenance_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/app/sspec_documentization_maintenance_perf_spec.spl:1:1: advice SSDOC-COV-001 [coverage] (-20): the authored requirement defines adverse behavior but no adverse scenario is named
  why: Specifications should explain behavior outside the happy path.
  improve: Add adverse-path scenarios required by the source, or record a reasoned suppression.
test/05_perf/app/sspec_documentization_maintenance_perf_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/app/sspec_documentization_maintenance_perf_spec.spl:49:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'scans one thousand representative pairs within the selected bound' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/05_perf/app/sspec_documentization_maintenance_perf_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps warm representative p95 below five hundred milliseconds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
