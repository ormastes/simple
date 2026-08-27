# ML / probabilistic evidence profile (E7)

> For QA authors capturing ML evaluation evidence: this spec proves the `MlRun`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ML / probabilistic evidence profile (E7)

For QA authors capturing ML evaluation evidence: this spec proves the `MlRun`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/spec/evidence/ml_profile_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

For QA authors capturing ML evaluation evidence: this spec proves the `MlRun`
metric/prediction model — validity rules, metric evaluation with tolerance,
confusion counts and scaled accuracy — and its fail-closed projection into
`CanonicalEvidence`. Audience: reviewers who must trust reported model metrics
without re-running the evaluation.

## Scenarios

### ML evidence profile

#### rejects a run with no recorded dataset hash as not reproducible

- Build a run whose dataset hash was never recorded
- Verify the run is rejected as invalid
   - Expected: ml_run_is_valid(run) is false
- Verify converting it to evidence fails to parse instead of emitting nodes
   - Expected: evidence.parse_ok is false
   - Expected: evidence.nodes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-EVD-007
step("Build a run whose dataset hash was never recorded")
val run = MlRun(
    model_id: "fraud-classifier",
    model_version: "2.4",
    dataset_hash: "",
    model_hash: "5eb63bbbe01eeed093cb22bb8f5acdc3",
    seed: "20260808-ml-1",
    framework: "torch"
)

step("Verify the run is rejected as invalid")
expect(ml_run_is_valid(run)).to_equal(false)

step("Verify converting it to evidence fails to parse instead of emitting nodes")
val evidence = ml_run_to_evidence(run, [accuracy_metric()], "ml/fraud-classifier")
expect(evidence.parse_ok).to_equal(false)
expect(evidence.nodes.len()).to_equal(0)
```

</details>

#### rejects a run with no recorded model hash as not reproducible

- rejects a run with no recorded model hash as not reproducible
- Build a run whose model hash was never recorded
- Verify the run is rejected as invalid
   - Expected: ml_run_is_valid(run) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a run with no recorded model hash as not reproducible")
step("Build a run whose model hash was never recorded")
val run = MlRun(
    model_id: "fraud-classifier",
    model_version: "2.4",
    dataset_hash: "d41d8cd98f00b204e9800998ecf8427e",
    model_hash: "",
    seed: "20260808-ml-1",
    framework: "torch"
)

step("Verify the run is rejected as invalid")
expect(ml_run_is_valid(run)).to_equal(false)
```

</details>

#### rejects a run with no recorded seed as not reproducible

- rejects a run with no recorded seed as not reproducible
- Build a run whose seed was never recorded
- Verify the run is rejected as invalid
   - Expected: ml_run_is_valid(run) is false
- Verify converting it to evidence fails to parse instead of emitting nodes
   - Expected: evidence.parse_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a run with no recorded seed as not reproducible")
step("Build a run whose seed was never recorded")
val run = MlRun(
    model_id: "fraud-classifier",
    model_version: "2.4",
    dataset_hash: "d41d8cd98f00b204e9800998ecf8427e",
    model_hash: "5eb63bbbe01eeed093cb22bb8f5acdc3",
    seed: "",
    framework: "torch"
)

step("Verify the run is rejected as invalid")
expect(ml_run_is_valid(run)).to_equal(false)

step("Verify converting it to evidence fails to parse instead of emitting nodes")
val evidence = ml_run_to_evidence(run, [accuracy_metric()], "ml/fraud-classifier")
expect(evidence.parse_ok).to_equal(false)
```

</details>

#### accepts a fully-tracked run and records its metrics as evidence nodes

- accepts a fully-tracked run and records its metrics as evidence nodes
- Convert a tracked run and its metrics to canonical evidence
- Verify the run parses and carries a node for the metric
   - Expected: evidence.parse_ok is true
   - Expected: metric_nodes equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a fully-tracked run and records its metrics as evidence nodes")
step("Convert a tracked run and its metrics to canonical evidence")
val evidence = ml_run_to_evidence(tracked_run(), [accuracy_metric()], "ml/fraud-classifier")

step("Verify the run parses and carries a node for the metric")
expect(evidence.parse_ok).to_equal(true)
var metric_nodes = 0
for node in evidence.nodes:
    if node.path == "ml.metric.accuracy":
        metric_nodes = metric_nodes + 1
expect(metric_nodes).to_equal(1)
```

</details>

#### requires every metric tolerance to carry a reason

- requires every metric tolerance to carry a reason
- Declare a metric whose tolerance has no recorded reason
- Verify the module itself rejects the metric as invalid
   - Expected: ml_metric_is_valid(metric) is false
- Verify evaluate_metrics reports it as a finding rather than silently checking the tolerance anyway
   - Expected: findings.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires every metric tolerance to carry a reason")
step("Declare a metric whose tolerance has no recorded reason")
val metric = MlMetric(name: "accuracy", value_scaled: 920, scale: 1000, tolerance_scaled: 10, reason: "")

step("Verify the module itself rejects the metric as invalid")
expect(ml_metric_is_valid(metric)).to_equal(false)

step("Verify evaluate_metrics reports it as a finding rather than silently checking the tolerance anyway")
val findings = evaluate_metrics([metric], [920])
expect(findings.len()).to_equal(1)
expect(findings[0]).to_contain("no recorded reason")
```

</details>

#### flags a metric outside its tolerance band

- flags a metric outside its tolerance band
- Declare an accuracy metric expecting 92.0% +/- 1.0%
- Evaluate it against an actual value far outside tolerance
- Verify a finding is reported
   - Expected: findings.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("flags a metric outside its tolerance band")
step("Declare an accuracy metric expecting 92.0% +/- 1.0%")
val metric = accuracy_metric()

step("Evaluate it against an actual value far outside tolerance")
val findings = evaluate_metrics([metric], [700])

step("Verify a finding is reported")
expect(findings.len()).to_equal(1)
expect(findings[0]).to_contain("accuracy")
```

</details>

#### passes a metric inside its tolerance band

- passes a metric inside its tolerance band
- Evaluate the accuracy metric against an actual value inside tolerance
- Verify no findings are reported
   - Expected: findings.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("passes a metric inside its tolerance band")
step("Evaluate the accuracy metric against an actual value inside tolerance")
val findings = evaluate_metrics([accuracy_metric()], [925])

step("Verify no findings are reported")
expect(findings.len()).to_equal(0)
```

</details>

#### reports a metrics/actual_values length mismatch as a finding, not a silent truncation

- reports a metrics/actual_values length mismatch as a finding, not a silent truncation
- Evaluate two metrics against only one actual value
- Verify the mismatch itself is reported
   - Expected: findings.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports a metrics/actual_values length mismatch as a finding, not a silent truncation")
step("Evaluate two metrics against only one actual value")
val findings = evaluate_metrics([accuracy_metric(), accuracy_metric()], [925])

step("Verify the mismatch itself is reported")
expect(findings.len()).to_equal(1)
expect(findings[0]).to_contain("length mismatch")
```

</details>

#### counts correct vs total predictions

- counts correct vs total predictions
- Compute confusion counts over a mixed prediction set
- Verify 3 of 4 predictions were correct
   - Expected: counts.0 equals `3`
   - Expected: counts.1 equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("counts correct vs total predictions")
step("Compute confusion counts over a mixed prediction set")
val counts = confusion_counts(predictions())

step("Verify 3 of 4 predictions were correct")
expect(counts.0).to_equal(3)
expect(counts.1).to_equal(4)
```

</details>

#### computes accuracy in parts-per-thousand

- computes accuracy in parts-per-thousand
- Compute accuracy over the same prediction set
- Verify it is 750 permille (3/4)
   - Expected: acc equals `750`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("computes accuracy in parts-per-thousand")
step("Compute accuracy over the same prediction set")
val acc = accuracy_permille(predictions())

step("Verify it is 750 permille (3/4)")
expect(acc).to_equal(750)
```

</details>

#### refuses accuracy on an empty prediction set instead of reporting a hollow zero

- refuses accuracy on an empty prediction set instead of reporting a hollow zero
- Compute accuracy over no predictions
- Verify it is refused, not reported as 0
   - Expected: acc equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses accuracy on an empty prediction set instead of reporting a hollow zero")
step("Compute accuracy over no predictions")
val acc = accuracy_permille([])

step("Verify it is refused, not reported as 0")
expect(acc).to_equal(-1)
```

</details>

#### feeds ml run evidence into compare_evidence against a closed oracle

- feeds ml run evidence into compare_evidence against a closed oracle
- Convert the tracked run and its metric to canonical evidence
- Declare a closed oracle covering every field the run emits, with a stated reason on the tolerance check
- Compare and verify the closed oracle passes because every emitted field is declared
   - Expected: result.status equals `EvidenceStatus.passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("feeds ml run evidence into compare_evidence against a closed oracle")
step("Convert the tracked run and its metric to canonical evidence")
val evidence = ml_run_to_evidence(tracked_run(), [accuracy_metric()], "ml/fraud-classifier")

step("Declare a closed oracle covering every field the run emits, with a stated reason on the tolerance check")
val oracle: OracleSpec = oracle_spec(
    "ml/fraud-classifier",
    [
        check_exact("ml.model_id", "fraud-classifier"),
        check_exact("ml.model_version", "2.4"),
        check_exact("ml.dataset_hash", "d41d8cd98f00b204e9800998ecf8427e"),
        check_exact("ml.model_hash", "5eb63bbbe01eeed093cb22bb8f5acdc3"),
        check_exact("ml.seed", "20260808-ml-1"),
        check_exact("ml.framework", "torch"),
        check_numeric_tolerance("ml.metric.accuracy", "920", 10, "held-out test split, run-to-run noise margin")
    ]
)

step("Compare and verify the closed oracle passes because every emitted field is declared")
val result = compare_evidence(evidence, oracle)
expect(result.status).to_equal(EvidenceStatus.passed)
```

</details>

#### checks a metric with check_numeric_tolerance and a stated reason

- checks a metric with check_numeric_tolerance and a stated reason
- Declare a single numeric-tolerance check with an explicit reason
- Verify the reason is carried on the check, not silently dropped
   - Expected: check.reason equals `held-out test split, run-to-run noise margin`
   - Expected: check.tolerance equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("checks a metric with check_numeric_tolerance and a stated reason")
step("Declare a single numeric-tolerance check with an explicit reason")
val check = check_numeric_tolerance("ml.metric.accuracy", "920", 10, "held-out test split, run-to-run noise margin")

step("Verify the reason is carried on the check, not silently dropped")
expect(check.reason).to_equal("held-out test split, run-to-run noise margin")
expect(check.tolerance).to_equal(10)
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
- `REQ-SSPEC-EVD-007`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e4ca75ca7563ba47fcf9d3dfd188ef55d4647bb6875eb12a555999d449dcf7e5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e4ca75ca7563ba47fcf9d3dfd188ef55d4647bb6875eb12a555999d449dcf7e5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e4ca75ca7563ba47fcf9d3dfd188ef55d4647bb6875eb12a555999d449dcf7e5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/spec/evidence/ml_profile_spec.spl
mirror: doc/06_spec/01_unit/lib/common/spec/evidence/ml_profile_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/spec/evidence/ml_profile_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/spec/evidence/ml_profile_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/spec/evidence/ml_profile_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/spec/evidence/ml_profile_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a run with no recorded model hash as not reproducible' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/spec/evidence/ml_profile_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires every metric tolerance to carry a reason' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/spec/evidence/ml_profile_spec.spl:153:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags a metric outside its tolerance band' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
