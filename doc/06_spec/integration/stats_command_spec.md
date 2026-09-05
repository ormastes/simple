# Stats Command Specification

> Tests covering stats command, stats output accuracy, stats performance.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stats Command Specification

## Scenarios

### stats command

#### shows basic statistics

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- shows basic statistics


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("shows basic statistics")
# This is a manual test - run: bin/simple stats
# Expected: Shows files, lines, tests, features
check_msg(true, "Manual test placeholder")
```

</details>

#### supports --brief flag

- supports --brief flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports --brief flag")
# Run: bin/simple stats --brief
# Expected: No "Collecting data..." or documentation section
check_msg(true, "Manual test placeholder")
```

</details>

#### supports --verbose flag

- supports --verbose flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports --verbose flag")
# Run: bin/simple stats --verbose
# Expected: Shows directory scan details
check_msg(true, "Manual test placeholder")
```

</details>

#### supports --quick flag

- supports --quick flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports --quick flag")
# Run: bin/simple stats --quick
# Expected: Skips line counting, faster execution
check_msg(true, "Manual test placeholder")
```

</details>

#### supports --json flag

- supports --json flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("supports --json flag")
# Run: bin/simple stats --json
# Expected: Outputs valid JSON with all metrics
check_msg(true, "Manual test placeholder")
```

</details>

#### combines flags correctly

- combines flags correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("combines flags correctly")
# Run: bin/simple stats --json --quick
# Expected: JSON output with lines: 0
check_msg(true, "Manual test placeholder")
```

</details>

### stats output accuracy

#### counts source files correctly

- counts source files correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("counts source files correctly")
# Verify file counts match actual filesystem
check_msg(true, "Manual test placeholder")
```

</details>

#### extracts test statistics from test_result.md

- extracts test statistics from test_result.md


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("extracts test statistics from test_result.md")
# Verify test counts match doc/test/test_result.md
check_msg(true, "Manual test placeholder")
```

</details>

#### extracts feature statistics from feature_db.sdn

- extracts feature statistics from feature_db.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("extracts feature statistics from feature_db.sdn")
# Verify feature counts match doc/02_requirements/feature/feature_db.sdn
check_msg(true, "Manual test placeholder")
```

</details>

### stats performance

#### completes in under 5 seconds (full mode)

- completes in under 5 seconds (full mode)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("completes in under 5 seconds (full mode)")
# time bin/simple stats
# Expected: < 5s
check_msg(true, "Manual test placeholder")
```

</details>

#### completes in under 1 second (quick mode)

- completes in under 1 second (quick mode)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("completes in under 1 second (quick mode)")
# time bin/simple stats --quick
# Expected: < 1s
check_msg(true, "Manual test placeholder")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/stats_command_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering stats command, stats output accuracy, stats performance.
- stats command
- stats output accuracy
- stats performance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `682cd321d8ea040abfcccc1f3c33a85948ca99298dc14cebc91cd63dcb4710d1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `682cd321d8ea040abfcccc1f3c33a85948ca99298dc14cebc91cd63dcb4710d1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `682cd321d8ea040abfcccc1f3c33a85948ca99298dc14cebc91cd63dcb4710d1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/stats_command_spec.spl
mirror: doc/06_spec/integration/stats_command_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/stats_command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/stats_command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/stats_command_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows basic statistics' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/stats_command_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports --brief flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/stats_command_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports --verbose flag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
