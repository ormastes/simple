# run_spec

> Purpose: Verify ML experiment tracking run creation, metric logging, artifacts and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# run_spec

Purpose: Verify ML experiment tracking run creation, metric logging, artifacts and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/ml/tracking/run_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify ML experiment tracking run creation, metric logging, artifacts and
run completion in offline mode.
Audience: ML tooling engineers who own std.ml.tracking.

## Scenarios

### ML experiment tracking run lifecycle

#### creates, logs, artifacts and finishes an offline tracking run

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates, logs, artifacts and finishes an offline tracking run
   - Expected: test_run.project equals `test-project`
   - Expected: test_run.name equals `test-run`
   - Expected: test_run.id != nil and test_run.id.len() > 0 is true
   - Expected: artifact.name equals `test-model`
   - Expected: artifact.type equals `model`
   - Expected: test_run.end_time != nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates, logs, artifacts and finishes an offline tracking run")
tracking.set_mode("offline")
val test_run = tracking.run(project: "test-project", name: "test-run", config: {"lr": 0.001}, tags: ["test"])

expect(test_run.project).to_equal("test-project")
expect(test_run.name).to_equal("test-run")
expect(test_run.id != nil and test_run.id.len() > 0).to_equal(true)

test_run.log({"loss": 0.5, "acc": 0.9}, step: 0)
test_run.log({"loss": 0.3, "acc": 0.95}, step: 1)

val artifact = tracking.Artifact("test-model", "model", "Test model artifact", {})
expect(artifact.name).to_equal("test-model")
expect(artifact.type).to_equal("model")

test_run.finish()
expect(test_run.end_time != nil).to_equal(true)
```

</details>

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `db3592617b2702b946096c531bc6fcb69458dc0383b4be224ae35587409559a1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db3592617b2702b946096c531bc6fcb69458dc0383b4be224ae35587409559a1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db3592617b2702b946096c531bc6fcb69458dc0383b4be224ae35587409559a1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/lib/std/ml/tracking/run_spec.spl
mirror: doc/06_spec/01_unit/lib/std/ml/tracking/run_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/std/ml/tracking/run_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/std/ml/tracking/run_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/std/ml/tracking/run_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates, logs, artifacts and finishes an offline tracking run' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
