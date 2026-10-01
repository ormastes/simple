# shutdown_spec

> Purpose: Prove that exit codes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# shutdown_spec

Purpose: Prove that exit codes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/test_runner_new/shutdown_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that exit codes.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### exit codes

#### should have distinct exit codes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should have distinct exit codes
- Verify: should have distinct exit codes
   - Expected: EXIT_SUCCESS equals `0`
   - Expected: EXIT_FAILURE equals `1`
   - Expected: EXIT_RESOURCE_SHUTDOWN equals `42`
   - Expected: EXIT_RECOVERY_FAILED equals `43`
   - Expected: all_different is true
   - Expected: diff2 is true
   - Expected: diff3 is true
   - Expected: diff4 is true
   - Expected: diff5 is true
   - Expected: diff6 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should have distinct exit codes")
step("Verify: should have distinct exit codes")
# @req: REQ-APP-TEST-RUNNER-NEW-001
expect(EXIT_SUCCESS).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(EXIT_FAILURE).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(EXIT_RESOURCE_SHUTDOWN).to_equal(42)  # oracle: 42 — named expected value from the requirement
expect(EXIT_RECOVERY_FAILED).to_equal(43)  # oracle: 43 — named expected value from the requirement

# All codes should be different
val all_different = EXIT_SUCCESS != EXIT_FAILURE
val diff2 = EXIT_SUCCESS != EXIT_RESOURCE_SHUTDOWN
val diff3 = EXIT_SUCCESS != EXIT_RECOVERY_FAILED
val diff4 = EXIT_FAILURE != EXIT_RESOURCE_SHUTDOWN
val diff5 = EXIT_FAILURE != EXIT_RECOVERY_FAILED
val diff6 = EXIT_RESOURCE_SHUTDOWN != EXIT_RECOVERY_FAILED

expect(all_different).to_equal(true)
expect(diff2).to_equal(true)
expect(diff3).to_equal(true)
expect(diff4).to_equal(true)
expect(diff5).to_equal(true)
expect(diff6).to_equal(true)
```

</details>

### shutdown_format_summary

#### should format summary with all fields

- should format summary with all fields
- Verify: should format summary with all fields
   - Expected: summary contains `cpu`
   - Expected: summary contains `10`
   - Expected: summary contains `2`
   - Expected: summary contains `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should format summary with all fields")
step("Verify: should format summary with all fields")
val summary = shutdown_format_summary("cpu", [], 10, 2, 3)

expect(summary.contains("cpu")).to_equal(true)
expect(summary.contains("10")).to_equal(true)
expect(summary.contains("2")).to_equal(true)
expect(summary.contains("3")).to_equal(true)
```

</details>

#### should include reason in summary

- should include reason in summary
- Verify: should include reason in summary
   - Expected: summary contains `memory`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should include reason in summary")
step("Verify: should include reason in summary")
val summary = shutdown_format_summary("memory", [], 0, 0, 0)

expect(summary.contains("memory")).to_equal(true)
```

</details>

#### should format with multiple completed files

- should format with multiple completed files
- Verify: should format with multiple completed files
   - Expected: summary contains `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should format with multiple completed files")
step("Verify: should format with multiple completed files")
val completed = ["a.spl", "b.spl", "c.spl"]
val summary = shutdown_format_summary("cpu", completed, 5, 1, 2)

expect(summary.contains("3")).to_equal(true)  # 3 completed files
```

</details>

#### should handle empty completed list

- should handle empty completed list
- Verify: should handle empty completed list
   - Expected: summary contains `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should handle empty completed list")
step("Verify: should handle empty completed list")
val completed: [text] = []
val summary = shutdown_format_summary("periodic", completed, 0, 0, 0)

expect(summary.contains("0")).to_equal(true)
```

</details>

#### should include passed count

- should include passed count
- Verify: should include passed count
   - Expected: summary contains `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should include passed count")
step("Verify: should include passed count")
val summary = shutdown_format_summary("test", [], 42, 0, 0)

expect(summary.contains("42")).to_equal(true)
```

</details>

#### should include failed count

- should include failed count
- Verify: should include failed count
   - Expected: summary contains `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should include failed count")
step("Verify: should include failed count")
val summary = shutdown_format_summary("test", [], 0, 7, 0)

expect(summary.contains("7")).to_equal(true)
```

</details>

#### should include skipped count

- should include skipped count
- Verify: should include skipped count
   - Expected: summary contains `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should include skipped count")
step("Verify: should include skipped count")
val summary = shutdown_format_summary("test", [], 0, 0, 9)

expect(summary.contains("9")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-TEST-RUNNER-NEW-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d63c7fe82c2ccc63132797047b39bab9ed0a3f25e39b887cf9b2b5d03eba1d66`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d63c7fe82c2ccc63132797047b39bab9ed0a3f25e39b887cf9b2b5d03eba1d66`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d63c7fe82c2ccc63132797047b39bab9ed0a3f25e39b887cf9b2b5d03eba1d66`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/app/test_runner_new/shutdown_spec.spl
mirror: doc/06_spec/unit/app/test_runner_new/shutdown_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/test_runner_new/shutdown_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/test_runner_new/shutdown_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/test_runner_new/shutdown_spec.spl:22:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should have distinct exit codes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/test_runner_new/shutdown_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should have distinct exit codes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/shutdown_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should format summary with all fields' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/test_runner_new/shutdown_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should format summary with all fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/shutdown_spec.spl:59:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include reason in summary' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/test_runner_new/shutdown_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should include reason in summary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/shutdown_spec.spl:67:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should format with multiple completed files' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/test_runner_new/shutdown_spec.spl:76:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle empty completed list' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/test_runner_new/shutdown_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include passed count' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
