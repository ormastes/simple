# progress_spec

> Tests for the progress() function that reports test execution status.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# progress_spec

Tests for the progress() function that reports test execution status.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/spec/progress_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for the progress() function that reports test execution status.

    Covers message formatting, percentage/step completion, timing display,
    and integration with slow tests and error scenarios.

## Scenarios

### Test Progress Reporting

#### progress function

#### prints progress message with timestamp

- prints progress message with timestamp


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prints progress message with timestamp")
progress("Starting test...")
expect true
```

</details>

#### shows elapsed time since test started

- shows elapsed time since test started


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows elapsed time since test started")
progress("Step 1")
progress("Step 2")
progress("Step 3")
expect true
```

</details>

#### can report percentage completion

- can report percentage completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can report percentage completion")
progress("Processing: 0%")
progress("Processing: 50%")
progress("Processing: 100%")
expect true
```

</details>

#### can report step-based completion

- can report step-based completion


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can report step-based completion")
val total_steps = 3
progress("Step 1 of 3")
progress("Step 2 of 3")
progress("Step 3 of 3")
expect true
```

</details>

#### progress with slow tests

#### shows progress during long operation

- shows progress during long operation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows progress during long operation")
progress("Loading modules...")
progress("Loaded 5/15 modules")
progress("Loaded 10/15 modules")
progress("Loaded 15/15 modules")
progress("Running verification...")
expect true
```

</details>

#### progress is optional

#### tests without progress calls work normally

- tests without progress calls work normally


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tests without progress calls work normally")
expect 1 + 1 == 2
```

</details>

#### progress calls can be conditional

- progress calls can be conditional


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("progress calls can be conditional")
val show_progress = true
if show_progress:
    progress("Progress enabled")
expect true
```

</details>

#### progress formatting

#### supports simple messages

- supports simple messages


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports simple messages")
progress("Simple message")
expect true
```

</details>

#### supports string interpolation

- supports string interpolation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports string interpolation")
val count = 42
val name = "items"
progress("Processed " + count.to_string() + " " + name)
expect true
```

</details>

#### handles multiline descriptions

- handles multiline descriptions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiline descriptions")
progress("Phase 1: Initialization")
progress("Phase 2: Processing")
progress("Phase 3: Finalization")
expect true
```

</details>

#### progress timing

#### shows time elapsed in human-readable format

- shows time elapsed in human-readable format


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shows time elapsed in human-readable format")
progress("Start")
progress("After some work")
expect true
```

</details>

#### progress with errors

#### progress output preserved when test fails

- progress output preserved when test fails


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("progress output preserved when test fails")
progress("Step 1 completed")
progress("Step 2 started")
expect true
```

</details>

### Progress API Design

#### has simple function signature

- has simple function signature


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has simple function signature")
progress("Message")
expect true
```

</details>

#### is available in all test contexts

- is available in all test contexts


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is available in all test contexts")
progress("Available in test")
expect true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `8edb46fe10b9887e3a16ce3bf477400e695e3c08d30a2dceea48266f2057f0b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8edb46fe10b9887e3a16ce3bf477400e695e3c08d30a2dceea48266f2057f0b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8edb46fe10b9887e3a16ce3bf477400e695e3c08d30a2dceea48266f2057f0b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/unit/spec/progress_spec.spl
mirror: doc/06_spec/unit/spec/progress_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/spec/progress_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/spec/progress_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/spec/progress_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints progress message with timestamp' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/spec/progress_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows elapsed time since test started' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/spec/progress_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can report percentage completion' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/spec/progress_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can report percentage completion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/spec/progress_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can report step-based completion' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
