# Smux Perf Specification

> Tests covering smux performance smoke.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Smux Perf Specification

## Scenarios

### smux performance smoke

<details>
<summary>Advanced: keeps reset plus initial session startup under the hosted smoke budget</summary>

#### keeps reset plus initial session startup under the hosted smoke budget _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps reset plus initial session startup under the hosted smoke budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("keeps reset plus initial session startup under the hosted smoke budget")
# warmup
var w = 0
while w < 3:
    val _ = _simulate_startup_ns()
    w = w + 1

# measure
var samples: [i64] = []
var m = 0
while m < 20:
    samples = samples.push(_simulate_startup_ns())
    m = m + 1

val avg_ms = _average(samples) / 1000000
val p95_ms = _percentile(samples, 95, 100) / 1000000
val iters = samples.len()
print "[perf] smux startup avg={avg_ms}ms p95={p95_ms}ms iters={iters}"
expect(avg_ms).to_be_less_than(200)
expect(p95_ms).to_be_less_than(200)
```

</details>


</details>

<details>
<summary>Advanced: keeps send plus capture p95 within the interactive smoke budget</summary>

#### keeps send plus capture p95 within the interactive smoke budget _(slow)_

- keeps send plus capture p95 within the interactive smoke budget


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("keeps send plus capture p95 within the interactive smoke budget")
# warmup
var w2 = 0
while w2 < 5:
    val _ = _simulate_send_capture_ns()
    w2 = w2 + 1

# measure
var samples2: [i64] = []
var seq = 0
while seq < 50:
    samples2 = samples2.push(_simulate_send_capture_ns())
    seq = seq + 1

val avg_ms2 = _average(samples2) / 1000000
val p95_ms2 = _percentile(samples2, 95, 100) / 1000000
val iters2 = samples2.len()
print "[perf] smux send/capture avg={avg_ms2}ms p95={p95_ms2}ms iters={iters2}"
expect(avg_ms2).to_be_less_than(20)
expect(p95_ms2).to_be_less_than(20)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/smux_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering smux performance smoke.
- smux performance smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 2 |
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

- Canonical SPipe generation for source `28a974cf38f4234044a5824baff6de414faa7981cb639afaed63186d34537317`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `28a974cf38f4234044a5824baff6de414faa7981cb639afaed63186d34537317`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `28a974cf38f4234044a5824baff6de414faa7981cb639afaed63186d34537317`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/05_perf/smux_perf_spec.spl
mirror: doc/06_spec/05_perf/smux_perf_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/smux_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/smux_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/smux_perf_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps reset plus initial session startup under the hosted smoke budget' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
