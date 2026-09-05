# Test Specification

> Tests covering test tool.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Specification

## Scenarios

### test tool

#### string tests

#### detects empty string with -z

- detects empty string with -z
   - Expected: s.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects empty string with -z")
val s = ""
expect(s.len()).to_equal(0)
```

</details>

#### detects non-empty string with -n

- detects non-empty string with -n


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects non-empty string with -n")
val s = "hello"
expect(s.len()).to_be_greater_than(0)
```

</details>

#### compares strings for equality

- compares strings for equality
   - Expected: "abc" equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares strings for equality")
expect("abc").to_equal("abc")
```

</details>

#### compares strings for inequality

- compares strings for inequality
   - Expected: "abc" != "def" is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compares strings for inequality")
expect("abc" != "def").to_equal(true)
```

</details>

#### integer tests

#### integer equality

- integer equality
   - Expected: 5 equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integer equality")
expect(5).to_equal(5)
```

</details>

#### integer less-than

- integer less-than
   - Expected: 3 < 5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integer less-than")
expect(3 < 5).to_equal(true)
```

</details>

#### integer greater-than

- integer greater-than
   - Expected: 7 > 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("integer greater-than")
expect(7 > 2).to_equal(true)
```

</details>

#### negation

#### negates true to false

- negates true to false
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negates true to false")
val result = if not true: 1 else: 0
expect(result).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/unit/tools/shell/test_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering test tool.
- test tool

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `58083bbeaaa4d28ee419964521959d717d875628de57d6c5b4573a03c3980bee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58083bbeaaa4d28ee419964521959d717d875628de57d6c5b4573a03c3980bee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58083bbeaaa4d28ee419964521959d717d875628de57d6c5b4573a03c3980bee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/tools/shell/test_spec.spl
mirror: doc/06_spec/unit/tools/shell/test_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/tools/shell/test_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/tools/shell/test_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/tools/shell/test_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/tools/shell/test_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects empty string with -z' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/shell/test_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects non-empty string with -n' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/tools/shell/test_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compares strings for equality' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
