# test_runner_output_parsing_spec

> Purpose: Prove that test runner output parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_runner_output_parsing_spec

Purpose: Prove that test runner output parsing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_output_parsing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that test runner output parsing.
Audience: APP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### test runner output parsing

#### uses the outer runner summary without double-counting skips

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses the outer runner summary without double-counting skips
- Verify: uses the outer runner summary without double-counting skips
   - Expected: passed equals `2`
   - Expected: failed equals `1`
   - Expected: skipped equals `1`
   - Expected: pending equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses the outer runner summary without double-counting skips")
step("Verify: uses the outer runner summary without double-counting skips")
# @req: REQ-APP-TEST-RUNNER-OUTPUT-PARSING-001
val output =
    "  PASS test/sample_spec.spl (2 passed, 1 skipped, 5ms)\n" +
    "Results: 3 total, 2 passed, 1 failed, 1 skipped\n"
val (passed, failed, skipped, pending) = parse_test_output(output)
expect(passed).to_equal(2)
expect(failed).to_equal(1)
expect(skipped).to_equal(1)
expect(pending).to_equal(0)
```

</details>

#### retains explicit single-file summary counts

- retains explicit single-file summary counts
- Verify: retains explicit single-file summary counts
   - Expected: passed equals `3`
   - Expected: failed equals `0`
   - Expected: skipped equals `2`
   - Expected: pending equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("retains explicit single-file summary counts")
step("Verify: retains explicit single-file summary counts")
val (passed, failed, skipped, pending) = parse_test_output(
    "Passed: 3\nFailed: 0\nSkipped: 2\nPending: 1\n"
)
expect(passed).to_equal(3)
expect(failed).to_equal(0)
expect(skipped).to_equal(2)
expect(pending).to_equal(1)
```

</details>

#### rejects internally inconsistent outer summaries

- rejects internally inconsistent outer summaries
- Verify: rejects internally inconsistent outer summaries
   - Expected: passed equals `0`
   - Expected: failed equals `0`
   - Expected: skipped equals `0`
   - Expected: pending equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects internally inconsistent outer summaries")
step("Verify: rejects internally inconsistent outer summaries")
val (passed, failed, skipped, pending) = parse_test_output(
    "Passed: 2\nFailed: 0\nResults: 9 total, 2 passed, 1 failed, 0 skipped\n"
)
expect(passed).to_equal(0)
expect(failed).to_equal(0)
expect(skipped).to_equal(0)
expect(pending).to_equal(0)
```

</details>

#### uses the last canonical outer summary

- uses the last canonical outer summary
- Verify: uses the last canonical outer summary
   - Expected: passed equals `3`
   - Expected: failed equals `0`
   - Expected: skipped equals `1`
   - Expected: pending equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses the last canonical outer summary")
step("Verify: uses the last canonical outer summary")
val (passed, failed, skipped, pending) = parse_test_output(
    "Results: 2 total, 1 passed, 1 failed\n" +
    "Results: 3 total, 3 passed, 0 failed, 1 skipped\n"
)
expect(passed).to_equal(3)
expect(failed).to_equal(0)
expect(skipped).to_equal(1)
expect(pending).to_equal(0)
```

</details>

#### ignores test-authored Results lines

- ignores test-authored Results lines
- Verify: ignores test-authored Results lines
   - Expected: passed equals `2`
   - Expected: failed equals `0`
   - Expected: skipped equals `0`
   - Expected: pending equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("ignores test-authored Results lines")
step("Verify: ignores test-authored Results lines")
val (passed, failed, skipped, pending) = parse_test_output(
    "Results: repository operation completed\n" +
    "Results: 2 total, 2 passed, 0 failed\n"
)
expect(passed).to_equal(2)
expect(failed).to_equal(0)
expect(skipped).to_equal(0)
expect(pending).to_equal(0)
```

</details>

#### uses a later direct summary after canonical-shaped authored output

- uses a later direct summary after canonical-shaped authored output
- Verify: uses a later direct summary after canonical-shaped authored output
   - Expected: passed equals `2`
   - Expected: failed equals `0`
   - Expected: skipped equals `0`
   - Expected: pending equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses a later direct summary after canonical-shaped authored output")
step("Verify: uses a later direct summary after canonical-shaped authored output")
val (passed, failed, skipped, pending) = parse_test_output(
    "Results: 9 total, 2 passed, 1 failed\n" +
    "Passed: 2\nFailed: 0\n"
)
expect(passed).to_equal(2)
expect(failed).to_equal(0)
expect(skipped).to_equal(0)
expect(pending).to_equal(0)
```

</details>

#### uses a later BDD summary after canonical-shaped authored output

- uses a later BDD summary after canonical-shaped authored output
- Verify: uses a later BDD summary after canonical-shaped authored output
   - Expected: passed equals `2`
   - Expected: failed equals `0`
   - Expected: skipped equals `0`
   - Expected: pending equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses a later BDD summary after canonical-shaped authored output")
step("Verify: uses a later BDD summary after canonical-shaped authored output")
val (passed, failed, skipped, pending) = parse_test_output(
    "8 examples, 3 failures\n" +
    "Results: 9 total, 2 passed, 1 failed, 4 skipped\n" +
    "2 examples, 0 failures\n"
)
expect(passed).to_equal(2)
expect(failed).to_equal(0)
expect(skipped).to_equal(0)
expect(pending).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
- `REQ-APP-TEST-RUNNER-OUTPUT-PARSING-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d6fd914c10c0e0cb27b1383db6c168acde12aad17b8b99cc70383cf43570b4b0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d6fd914c10c0e0cb27b1383db6c168acde12aad17b8b99cc70383cf43570b4b0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d6fd914c10c0e0cb27b1383db6c168acde12aad17b8b99cc70383cf43570b4b0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/test_runner_output_parsing_spec.spl
mirror: doc/06_spec/01_unit/app/test_runner_output_parsing_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/test_runner_output_parsing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/test_runner_output_parsing_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/test_runner_output_parsing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 28 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/test_runner_output_parsing_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the outer runner summary without double-counting skips' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_output_parsing_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains explicit single-file summary counts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/test_runner_output_parsing_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects internally inconsistent outer summaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
