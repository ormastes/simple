# Claude Full FpsTracker

> Checks FPS metric aggregation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full FpsTracker

Checks FPS metric aggregation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/fpsTracker_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks FPS metric aggregation.

## Scenarios

### Claude full FpsTracker

#### should report no metrics until time advances

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should report no metrics until time advances
   - Expected: FpsTracker.new().getMetrics().averageFpsHundredths equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should report no metrics until time advances")
expect(FpsTracker.new().getMetrics().averageFpsHundredths).to_equal(0)
```

</details>

#### should compute average and low one percent FPS

- should compute average and low one percent FPS
   - Expected: metrics.averageFpsHundredths equals `1500`
   - Expected: metrics.low1PctFpsHundredths equals `4000`
   - Expected: fpsTrackerSourceLinesModeled() equals `47`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should compute average and low one percent FPS")
var tracker = FpsTracker.new()
tracker = tracker.record(16, 100)
tracker = tracker.record(20, 200)
tracker = tracker.record(25, 300)
val metrics = tracker.getMetrics()
expect(metrics.averageFpsHundredths).to_equal(1500)
expect(metrics.low1PctFpsHundredths).to_equal(4000)
expect(fpsTrackerSourceLinesModeled()).to_equal(47)
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e92bcafca3cf42f6a616ce22829e664c5d8c4c07aa35ba05663d0f738dc2d4ad`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e92bcafca3cf42f6a616ce22829e664c5d8c4c07aa35ba05663d0f738dc2d4ad`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e92bcafca3cf42f6a616ce22829e664c5d8c4c07aa35ba05663d0f738dc2d4ad`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/utils/fpsTracker_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/utils/fpsTracker_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/utils/fpsTracker_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/utils/fpsTracker_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/utils/fpsTracker_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/utils/fpsTracker_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report no metrics until time advances' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/fpsTracker_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should report no metrics until time advances' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/utils/fpsTracker_spec.spl:23:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should compute average and low one percent FPS' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/utils/fpsTracker_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should compute average and low one percent FPS' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
