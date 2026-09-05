# Simulation + performance/statistics evidence profiles (E7b)

> For QA authors capturing simulation and performance evidence: this spec proves

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simulation + performance/statistics evidence profiles (E7b)

For QA authors capturing simulation and performance evidence: this spec proves

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/spec/evidence/simulation_profile_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

For QA authors capturing simulation and performance evidence: this spec proves
the `SimulationRun` timeline/invariant/KPI model and the `SampleSet` statistics
profile — validity rules, scaled fixed-point statistics, tolerance checks — and
their fail-closed projection into `CanonicalEvidence`. Audience: reviewers who
must trust numeric performance claims without re-deriving the statistics.

## Scenarios

### Simulation evidence profile

#### rejects a run with no recorded seed as not reproducible

- Build a run whose seed was never recorded
- Verify the run is rejected as invalid
   - Expected: simulation_run_is_valid(run) is false
- Verify converting it to evidence fails to parse instead of emitting nodes
   - Expected: evidence.parse_ok is false
   - Expected: evidence.nodes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-EVD-007B
step("Build a run whose seed was never recorded")
val run = SimulationRun(
    model_id: "thermal-plant",
    model_version: "3.1",
    seed: "",
    solver: "rk4",
    time_step_us: 1000,
    termination: "steady_state",
    environment: "ci-sim-01"
)

step("Verify the run is rejected as invalid")
expect(simulation_run_is_valid(run)).to_equal(false)

step("Verify converting it to evidence fails to parse instead of emitting nodes")
val evidence = simulation_to_evidence(run, temperature_timeline(), "sim/thermal-plant")
expect(evidence.parse_ok).to_equal(false)
expect(evidence.nodes.len()).to_equal(0)
```

</details>

#### accepts a seeded run and records its timeline as evidence nodes

- accepts a seeded run and records its timeline as evidence nodes
- Convert a seeded run and its timeline to canonical evidence
- Verify the run parses and carries a timeline node per sample
   - Expected: evidence.parse_ok is true
   - Expected: timeline_nodes equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a seeded run and records its timeline as evidence nodes")
step("Convert a seeded run and its timeline to canonical evidence")
val evidence = simulation_to_evidence(seeded_run(), temperature_timeline(), "sim/thermal-plant")

step("Verify the run parses and carries a timeline node per sample")
expect(evidence.parse_ok).to_equal(true)
var timeline_nodes = 0
for node in evidence.nodes:
    if node.path == "simulation.timeline.temp_c_milli":
        timeline_nodes = timeline_nodes + 1
expect(timeline_nodes).to_equal(4)
```

</details>

#### flags an invariant breach at any timeline point, even when the run ends clean

- flags an invariant breach at any timeline point, even when the run ends clean
- Declare an invariant that the temperature never exceeds 55000 milli-C
- Check the invariant against a timeline that spikes mid-run then settles
- Verify both breaches (t=2000us and the still-hot t=3000us) are reported, not just the worst one
   - Expected: findings.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("flags an invariant breach at any timeline point, even when the run ends clean")
step("Declare an invariant that the temperature never exceeds 55000 milli-C")
val invariants = [
    InvariantSpec(name: "temp-ceiling", signal: "temp_c_milli", min_value: 0, max_value: 55000)
]

step("Check the invariant against a timeline that spikes mid-run then settles")
val findings = check_invariants(temperature_timeline(), invariants)

step("Verify both breaches (t=2000us and the still-hot t=3000us) are reported, not just the worst one")
expect(findings.len()).to_equal(2)
expect(findings[0]).to_contain("temp-ceiling")
expect(findings[0]).to_contain("t=2000us")
```

</details>

#### passes an invariant that holds at every timeline point

- passes an invariant that holds at every timeline point
- Declare a wider invariant that covers the whole run
- Check it against the same timeline
- Verify no findings are reported
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes an invariant that holds at every timeline point")
step("Declare a wider invariant that covers the whole run")
val invariants = [
    InvariantSpec(name: "temp-ceiling", signal: "temp_c_milli", min_value: 0, max_value: 70000)
]

step("Check it against the same timeline")
val findings = check_invariants(temperature_timeline(), invariants)

step("Verify no findings are reported")
expect(findings.len()).to_equal(0)
```

</details>

#### evaluates a KPI against the settled end-of-run value

- evaluates a KPI against the settled end-of-run value
- Declare a KPI expecting the settled temperature near 58000 milli-C
- Evaluate the KPI against the timeline
- Verify it passes because the last sample is within tolerance
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("evaluates a KPI against the settled end-of-run value")
step("Declare a KPI expecting the settled temperature near 58000 milli-C")
val kpis = [
    KpiSpec(name: "settled-temp", signal: "temp_c_milli", expected: 58500, tolerance: 1000, reason: "steady-state target with sensor noise margin")
]

step("Evaluate the KPI against the timeline")
val findings = evaluate_kpis(temperature_timeline(), kpis)

step("Verify it passes because the last sample is within tolerance")
expect(findings.len()).to_equal(0)
```

</details>

#### requires every KPI tolerance to carry a reason

- requires every KPI tolerance to carry a reason
- Declare a KPI whose tolerance has no recorded reason
- Verify the reason field is empty, which downstream policy must reject before trusting the KPI
   - Expected: kpi.reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires every KPI tolerance to carry a reason")
step("Declare a KPI whose tolerance has no recorded reason")
val kpi = KpiSpec(name: "settled-temp", signal: "temp_c_milli", expected: 58500, tolerance: 1000, reason: "")

step("Verify the reason field is empty, which downstream policy must reject before trusting the KPI")
expect(kpi.reason).to_equal("")
```

</details>

#### feeds simulation evidence into compare_evidence against a closed oracle

- feeds simulation evidence into compare_evidence against a closed oracle
- Convert the seeded run to canonical evidence
- Declare a closed oracle covering every field the run emits, ignoring nothing
- Compare — the closed oracle must fail because it does not declare every emitted field
   - Expected: result.status equals `EvidenceStatus.failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("feeds simulation evidence into compare_evidence against a closed oracle")
step("Convert the seeded run to canonical evidence")
val evidence = simulation_to_evidence(seeded_run(), temperature_timeline(), "sim/thermal-plant")

step("Declare a closed oracle covering every field the run emits, ignoring nothing")
val oracle: OracleSpec = oracle_spec(
    "sim/thermal-plant",
    [
        check_numeric_tolerance("simulation.time_step_us", "1000", 0, "fixed solver step"),
        check_numeric_tolerance("simulation.timeline.temp_c_milli", "20000", 0, "first sample checked exactly")
    ]
)

step("Compare — the closed oracle must fail because it does not declare every emitted field")
val result = compare_evidence(evidence, oracle)
expect(result.status).to_equal(EvidenceStatus.failed)
```

</details>

### Performance / statistics evidence profile

#### rejects an empty sample set instead of reporting a passing zero

- rejects an empty sample set instead of reporting a passing zero
- Build a sample set with no recorded samples
- Verify it is rejected as invalid
   - Expected: sample_set_is_valid(empty) is false
- Verify converting it to evidence fails to parse instead of emitting a zeroed node set
   - Expected: evidence.parse_ok is false
   - Expected: evidence.nodes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an empty sample set instead of reporting a passing zero")
step("Build a sample set with no recorded samples")
val empty = SampleSet(metric: "request_latency", unit: "us", samples: [], scale: 1)

step("Verify it is rejected as invalid")
expect(sample_set_is_valid(empty)).to_equal(false)

step("Verify converting it to evidence fails to parse instead of emitting a zeroed node set")
val evidence = samples_to_evidence(empty, "perf/request_latency")
expect(evidence.parse_ok).to_equal(false)
expect(evidence.nodes.len()).to_equal(0)
```

</details>

#### computes count, min, max, and mean over a sample set

- computes count, min, max, and mean over a sample set
- Build a sample set of recorded latencies
- Compute the basic statistics
   - Expected: sample_count(set) equals `10`
   - Expected: sample_min(set) equals `1200`
   - Expected: sample_max(set) equals `5000`
- Verify the mean falls between the min and max
   - Expected: mean > sample_min(set) is true
   - Expected: mean < sample_max(set) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("computes count, min, max, and mean over a sample set")
step("Build a sample set of recorded latencies")
val set = latency_samples()

step("Compute the basic statistics")
expect(sample_count(set)).to_equal(10)
expect(sample_min(set)).to_equal(1200)
expect(sample_max(set)).to_equal(5000)

step("Verify the mean falls between the min and max")
val mean = sample_mean_scaled(set)
expect(mean > sample_min(set)).to_equal(true)
expect(mean < sample_max(set)).to_equal(true)
```

</details>

#### computes a nearest-rank percentile once enough samples are declared

- computes a nearest-rank percentile once enough samples are declared
- Compute the p50 of the latency samples with a floor of 5 samples
- Verify the median lands near the typical ~1270-1300us cluster, not the outlier
   - Expected: p50 >= 1250 is true
   - Expected: p50 <= 1310 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("computes a nearest-rank percentile once enough samples are declared")
step("Compute the p50 of the latency samples with a floor of 5 samples")
val p50 = sample_percentile(latency_samples().samples, 50, 5)

step("Verify the median lands near the typical ~1270-1300us cluster, not the outlier")
expect(p50 >= 1250).to_equal(true)
expect(p50 <= 1310).to_equal(true)
```

</details>

#### refuses a percentile computed from fewer samples than the declared minimum

- refuses a percentile computed from fewer samples than the declared minimum
- Request a p99 but require at least 100 samples, more than were recorded
- Verify the percentile is refused, not reported as an under-supported estimate
   - Expected: p99 equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses a percentile computed from fewer samples than the declared minimum")
step("Request a p99 but require at least 100 samples, more than were recorded")
val p99 = sample_percentile(latency_samples().samples, 99, 100)

step("Verify the percentile is refused, not reported as an under-supported estimate")
expect(p99).to_equal(-1)
```

</details>

#### reports a distribution as within tolerance when the mean is close enough to expected

- reports a distribution as within tolerance when the mean is close enough to expected
- Check the latency distribution against an expected mean of 1646us +/- 50us (mean including the one outlier)
- Verify it is accepted
   - Expected: within is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports a distribution as within tolerance when the mean is close enough to expected")
step("Check the latency distribution against an expected mean of 1646us +/- 50us (mean including the one outlier)")
val within = distribution_within(latency_samples(), 1646, 50)

step("Verify it is accepted")
expect(within).to_equal(true)
```

</details>

#### feeds a sample-set summary into compare_evidence with a numeric-tolerance KPI check

- feeds a sample-set summary into compare_evidence with a numeric-tolerance KPI check
- Convert the latency sample set to canonical evidence
- Declare an oracle checking the mean is within tolerance of an expected latency, with a stated reason
- Compare and verify the closed oracle passes because every emitted field is declared
   - Expected: result.status equals `EvidenceStatus.passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("feeds a sample-set summary into compare_evidence with a numeric-tolerance KPI check")
step("Convert the latency sample set to canonical evidence")
val evidence = samples_to_evidence(latency_samples(), "perf/request_latency")

step("Declare an oracle checking the mean is within tolerance of an expected latency, with a stated reason")
val oracle: OracleSpec = oracle_spec(
    "perf/request_latency",
    [
        check_numeric_tolerance("sample_set.mean_scaled", "1646", 50, "warm-cache latency budget with jitter margin, mean includes one outlier"),
        check_numeric_tolerance("sample_set.count", "10", 0, "fixed sample batch size"),
        check_numeric_tolerance("sample_set.min", "1200", 0, "fastest recorded request"),
        check_numeric_tolerance("sample_set.max", "5000", 0, "slowest recorded request, includes one outlier"),
        check_exact("sample_set.metric", "request_latency"),
        check_exact("sample_set.unit", "us"),
        check_numeric_tolerance("sample_set.scale", "1", 0, "raw microseconds, unscaled")
    ]
)

step("Compare and verify the closed oracle passes because every emitted field is declared")
val result = compare_evidence(evidence, oracle)
expect(result.status).to_equal(EvidenceStatus.passed)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-SSPEC-EVD-007B`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9c57b4e42e09fd5722504b82153c6ac1797dd619c9c72a3db50784137140e99b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c57b4e42e09fd5722504b82153c6ac1797dd619c9c72a3db50784137140e99b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c57b4e42e09fd5722504b82153c6ac1797dd619c9c72a3db50784137140e99b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/spec/evidence/simulation_profile_spec.spl
mirror: doc/06_spec/01_unit/lib/common/spec/evidence/simulation_profile_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/spec/evidence/simulation_profile_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/spec/evidence/simulation_profile_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/spec/evidence/simulation_profile_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/spec/evidence/simulation_profile_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags an invariant breach at any timeline point, even when the run ends clean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/spec/evidence/simulation_profile_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes an invariant that holds at every timeline point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/spec/evidence/simulation_profile_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'evaluates a KPI against the settled end-of-run value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
