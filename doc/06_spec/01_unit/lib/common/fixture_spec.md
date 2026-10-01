# Fixture Specification

> Tests covering Fixture Tests, using test data, computed fixtures.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fixture Specification

## Scenarios

### Fixture Tests

### using test data

#### tests with fixture value

- tests with fixture value


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tests with fixture value")
val fixture_value = 42
expect fixture_value == 42
```

</details>

#### tests with fixture string

- tests with fixture string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tests with fixture string")
val fixture_name = "test_user"
expect fixture_name == "test_user"
```

</details>

#### tests with fixture list

- tests with fixture list


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tests with fixture list")
val fixture_list = [1, 2, 3]
expect fixture_list[0] == 1
expect fixture_list[1] == 2
expect fixture_list[2] == 3
```

</details>

### computed fixtures

#### uses computed test data

- uses computed test data


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses computed test data")
val base = 10
val multiplier = 5
val expected = base * multiplier
expect expected == 50
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/fixture_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Fixture Tests, using test data, computed fixtures.
- Fixture Tests
- using test data
- computed fixtures

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `ee0c2e1ae87b3379bec692bddf407f972efb2304e9866bf21c22e100a42dc39a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee0c2e1ae87b3379bec692bddf407f972efb2304e9866bf21c22e100a42dc39a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee0c2e1ae87b3379bec692bddf407f972efb2304e9866bf21c22e100a42dc39a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/fixture_spec.spl
mirror: doc/06_spec/01_unit/lib/common/fixture_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/fixture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/fixture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/fixture_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tests with fixture value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/fixture_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tests with fixture string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/fixture_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tests with fixture list' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
