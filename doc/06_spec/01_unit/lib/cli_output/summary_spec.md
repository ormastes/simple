# Summary Specification

> Tests covering cli_output.summary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Summary Specification

## Scenarios

### cli_output.summary

#### format_summary

#### should format all-pass summary

- should format all-pass summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should format all-pass summary")
val result = format_summary(47, 0, 0, 0, 1340)
expect(result).to_contain("47 passed")
expect(result).to_contain("1.34s")
```

</details>

#### should format summary with failures

- should format summary with failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should format summary with failures")
val result = format_summary(45, 2, 0, 0, 1340)
expect(result).to_contain("45 passed")
expect(result).to_contain("2 failed")
```

</details>

#### should format summary with warnings

- should format summary with warnings


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should format summary with warnings")
val result = format_summary(45, 2, 3, 0, 1340)
expect(result).to_contain("45 passed")
expect(result).to_contain("2 failed")
expect(result).to_contain("3 warnings")
```

</details>

#### should include duration in summary

- should include duration in summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should include duration in summary")
val result = format_summary(10, 0, 0, 0, 500)
expect(result).to_contain("500ms")
```

</details>

#### format_duration

#### should format sub-second durations

- should format sub-second durations
   - Expected: result equals `450ms`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should format sub-second durations")
val result = format_duration(450)
expect(result).to_equal("450ms")
```

</details>

#### should format seconds with centiseconds

- should format seconds with centiseconds
   - Expected: result equals `1.34s`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should format seconds with centiseconds")
val result = format_duration(1340)
expect(result).to_equal("1.34s")
```

</details>

#### should format minutes and seconds

- should format minutes and seconds
   - Expected: result equals `2m 15s`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should format minutes and seconds")
val result = format_duration(135000)
expect(result).to_equal("2m 15s")
```

</details>

#### should format exact minutes

- should format exact minutes
   - Expected: result equals `2m`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should format exact minutes")
val result = format_duration(120000)
expect(result).to_equal("2m")
```

</details>

#### print helpers

#### should print error without crashing

- should print error without crashing
   - Expected: result equals `error: test error message`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should print error without crashing")
val result = print_error_now("test error message")
expect(result).to_equal("error: test error message")
```

</details>

#### should suppress warning when not strict

- should suppress warning when not strict
   - Expected: result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should suppress warning when not strict")
val result = print_warning_now("test warning", false)
expect(result).to_equal("")
```

</details>

#### should print warning when strict

- should print warning when strict
   - Expected: result equals `warning: test warning`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should print warning when strict")
val result = print_warning_now("test warning", true)
expect(result).to_equal("warning: test warning")
```

</details>

#### should print log hint without crashing

- should print log hint without crashing
   - Expected: result equals `Full log: build/log/test/latest.log`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should print log hint without crashing")
val result = print_log_hint("test")
expect(result).to_equal("Full log: build/log/test/latest.log")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/cli_output/summary_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering cli_output.summary.
- cli_output.summary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a36af4a3ee2b477fdf2d30ec50314c001709c3daf93d80217085dcb535c86c78`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a36af4a3ee2b477fdf2d30ec50314c001709c3daf93d80217085dcb535c86c78`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a36af4a3ee2b477fdf2d30ec50314c001709c3daf93d80217085dcb535c86c78`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/cli_output/summary_spec.spl
mirror: doc/06_spec/01_unit/lib/cli_output/summary_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/cli_output/summary_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/cli_output/summary_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/cli_output/summary_spec.spl:78:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should format all-pass summary' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/cli_output/summary_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should format all-pass summary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/cli_output/summary_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should format summary with failures' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/cli_output/summary_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should format summary with failures' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/cli_output/summary_spec.spl:92:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should format summary with warnings' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/cli_output/summary_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should format summary with warnings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/cli_output/summary_spec.spl:100:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should include duration in summary' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/cli_output/summary_spec.spl:107:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should format sub-second durations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/cli_output/summary_spec.spl:113:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should format seconds with centiseconds' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
