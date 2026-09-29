# Bug Severity Specification

> Tests covering severity_to_string, parse_severity, severity roundtrip, status_to_string, parse_status, status roundtrip, cross-function interaction.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bug Severity Specification

## Scenarios

### severity_to_string

#### converts P0 to string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- converts P0 to string
   - Expected: severity_to_string(BugSeverity.P0) equals `P0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts P0 to string")
expect(severity_to_string(BugSeverity.P0)).to_equal("P0")
```

</details>

#### converts P1 to string

- converts P1 to string
   - Expected: severity_to_string(BugSeverity.P1) equals `P1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts P1 to string")
expect(severity_to_string(BugSeverity.P1)).to_equal("P1")
```

</details>

#### converts P2 to string

- converts P2 to string
   - Expected: severity_to_string(BugSeverity.P2) equals `P2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts P2 to string")
expect(severity_to_string(BugSeverity.P2)).to_equal("P2")
```

</details>

#### converts P3 to string

- converts P3 to string
   - Expected: severity_to_string(BugSeverity.P3) equals `P3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts P3 to string")
expect(severity_to_string(BugSeverity.P3)).to_equal("P3")
```

</details>

#### converts Important to string

- converts Important to string
   - Expected: severity_to_string(BugSeverity.Important) equals `Important`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Important to string")
expect(severity_to_string(BugSeverity.Important)).to_equal("Important")
```

</details>

### parse_severity

#### parses P0

- parses P0
   - Expected: severity_to_string(sev) equals `P0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses P0")
val sev = parse_severity("P0")
expect(severity_to_string(sev)).to_equal("P0")
```

</details>

#### parses P1

- parses P1
   - Expected: severity_to_string(sev) equals `P1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses P1")
val sev = parse_severity("P1")
expect(severity_to_string(sev)).to_equal("P1")
```

</details>

#### parses P2

- parses P2
   - Expected: severity_to_string(sev) equals `P2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses P2")
val sev = parse_severity("P2")
expect(severity_to_string(sev)).to_equal("P2")
```

</details>

#### parses P3

- parses P3
   - Expected: severity_to_string(sev) equals `P3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses P3")
val sev = parse_severity("P3")
expect(severity_to_string(sev)).to_equal("P3")
```

</details>

#### parses Important

- parses Important
   - Expected: severity_to_string(sev) equals `Important`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses Important")
val sev = parse_severity("Important")
expect(severity_to_string(sev)).to_equal("Important")
```

</details>

#### defaults to P3 for unknown string

- defaults to P3 for unknown string
   - Expected: severity_to_string(sev) equals `P3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to P3 for unknown string")
val sev = parse_severity("Unknown")
expect(severity_to_string(sev)).to_equal("P3")
```

</details>

#### defaults to P3 for empty string

- defaults to P3 for empty string
   - Expected: severity_to_string(sev) equals `P3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to P3 for empty string")
val sev = parse_severity("")
expect(severity_to_string(sev)).to_equal("P3")
```

</details>

#### defaults to P3 for lowercase

- defaults to P3 for lowercase
   - Expected: severity_to_string(sev) equals `P3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to P3 for lowercase")
val sev = parse_severity("p0")
expect(severity_to_string(sev)).to_equal("P3")
```

</details>

#### defaults to P3 for random text

- defaults to P3 for random text
   - Expected: severity_to_string(sev) equals `P3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to P3 for random text")
val sev = parse_severity("critical")
expect(severity_to_string(sev)).to_equal("P3")
```

</details>

### severity roundtrip

#### P0 roundtrips through string

- P0 roundtrips through string
   - Expected: severity_to_string(back) equals `P0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("P0 roundtrips through string")
val s = severity_to_string(BugSeverity.P0)
val back = parse_severity(s)
expect(severity_to_string(back)).to_equal("P0")
```

</details>

#### P1 roundtrips through string

- P1 roundtrips through string
   - Expected: severity_to_string(back) equals `P1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("P1 roundtrips through string")
val s = severity_to_string(BugSeverity.P1)
val back = parse_severity(s)
expect(severity_to_string(back)).to_equal("P1")
```

</details>

#### P2 roundtrips through string

- P2 roundtrips through string
   - Expected: severity_to_string(back) equals `P2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("P2 roundtrips through string")
val s = severity_to_string(BugSeverity.P2)
val back = parse_severity(s)
expect(severity_to_string(back)).to_equal("P2")
```

</details>

#### P3 roundtrips through string

- P3 roundtrips through string
   - Expected: severity_to_string(back) equals `P3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("P3 roundtrips through string")
val s = severity_to_string(BugSeverity.P3)
val back = parse_severity(s)
expect(severity_to_string(back)).to_equal("P3")
```

</details>

#### Important roundtrips through string

- Important roundtrips through string
   - Expected: severity_to_string(back) equals `Important`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Important roundtrips through string")
val s = severity_to_string(BugSeverity.Important)
val back = parse_severity(s)
expect(severity_to_string(back)).to_equal("Important")
```

</details>

### status_to_string

#### converts Open to string

- converts Open to string
   - Expected: status_to_string(BugStatus.Open) equals `Open`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Open to string")
expect(status_to_string(BugStatus.Open)).to_equal("Open")
```

</details>

#### converts Investigating to string

- converts Investigating to string
   - Expected: status_to_string(BugStatus.Investigating) equals `Investigating`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Investigating to string")
expect(status_to_string(BugStatus.Investigating)).to_equal("Investigating")
```

</details>

#### converts Confirmed to string

- converts Confirmed to string
   - Expected: status_to_string(BugStatus.Confirmed) equals `Confirmed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Confirmed to string")
expect(status_to_string(BugStatus.Confirmed)).to_equal("Confirmed")
```

</details>

#### converts Fixed to string

- converts Fixed to string
   - Expected: status_to_string(BugStatus.Fixed) equals `Fixed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Fixed to string")
expect(status_to_string(BugStatus.Fixed)).to_equal("Fixed")
```

</details>

#### converts Closed to string

- converts Closed to string
   - Expected: status_to_string(BugStatus.Closed) equals `Closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Closed to string")
expect(status_to_string(BugStatus.Closed)).to_equal("Closed")
```

</details>

#### converts Wontfix to string

- converts Wontfix to string
   - Expected: status_to_string(BugStatus.Wontfix) equals `Wontfix`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Wontfix to string")
expect(status_to_string(BugStatus.Wontfix)).to_equal("Wontfix")
```

</details>

### parse_status

#### parses Open

- parses Open
   - Expected: status_to_string(st) equals `Open`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses Open")
val st = parse_status("Open")
expect(status_to_string(st)).to_equal("Open")
```

</details>

#### parses Investigating

- parses Investigating
   - Expected: status_to_string(st) equals `Investigating`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses Investigating")
val st = parse_status("Investigating")
expect(status_to_string(st)).to_equal("Investigating")
```

</details>

#### parses Confirmed

- parses Confirmed
   - Expected: status_to_string(st) equals `Confirmed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses Confirmed")
val st = parse_status("Confirmed")
expect(status_to_string(st)).to_equal("Confirmed")
```

</details>

#### parses Fixed

- parses Fixed
   - Expected: status_to_string(st) equals `Fixed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses Fixed")
val st = parse_status("Fixed")
expect(status_to_string(st)).to_equal("Fixed")
```

</details>

#### parses Closed

- parses Closed
   - Expected: status_to_string(st) equals `Closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses Closed")
val st = parse_status("Closed")
expect(status_to_string(st)).to_equal("Closed")
```

</details>

#### parses Wontfix

- parses Wontfix
   - Expected: status_to_string(st) equals `Wontfix`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses Wontfix")
val st = parse_status("Wontfix")
expect(status_to_string(st)).to_equal("Wontfix")
```

</details>

#### defaults to Open for unknown string

- defaults to Open for unknown string
   - Expected: status_to_string(st) equals `Open`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to Open for unknown string")
val st = parse_status("Unknown")
expect(status_to_string(st)).to_equal("Open")
```

</details>

#### defaults to Open for empty string

- defaults to Open for empty string
   - Expected: status_to_string(st) equals `Open`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to Open for empty string")
val st = parse_status("")
expect(status_to_string(st)).to_equal("Open")
```

</details>

#### defaults to Open for lowercase

- defaults to Open for lowercase
   - Expected: status_to_string(st) equals `Open`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to Open for lowercase")
val st = parse_status("open")
expect(status_to_string(st)).to_equal("Open")
```

</details>

#### defaults to Open for random text

- defaults to Open for random text
   - Expected: status_to_string(st) equals `Open`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to Open for random text")
val st = parse_status("resolved")
expect(status_to_string(st)).to_equal("Open")
```

</details>

### status roundtrip

#### Open roundtrips through string

- Open roundtrips through string
   - Expected: status_to_string(back) equals `Open`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Open roundtrips through string")
val s = status_to_string(BugStatus.Open)
val back = parse_status(s)
expect(status_to_string(back)).to_equal("Open")
```

</details>

#### Investigating roundtrips through string

- Investigating roundtrips through string
   - Expected: status_to_string(back) equals `Investigating`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Investigating roundtrips through string")
val s = status_to_string(BugStatus.Investigating)
val back = parse_status(s)
expect(status_to_string(back)).to_equal("Investigating")
```

</details>

#### Confirmed roundtrips through string

- Confirmed roundtrips through string
   - Expected: status_to_string(back) equals `Confirmed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Confirmed roundtrips through string")
val s = status_to_string(BugStatus.Confirmed)
val back = parse_status(s)
expect(status_to_string(back)).to_equal("Confirmed")
```

</details>

#### Fixed roundtrips through string

- Fixed roundtrips through string
   - Expected: status_to_string(back) equals `Fixed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Fixed roundtrips through string")
val s = status_to_string(BugStatus.Fixed)
val back = parse_status(s)
expect(status_to_string(back)).to_equal("Fixed")
```

</details>

#### Closed roundtrips through string

- Closed roundtrips through string
   - Expected: status_to_string(back) equals `Closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Closed roundtrips through string")
val s = status_to_string(BugStatus.Closed)
val back = parse_status(s)
expect(status_to_string(back)).to_equal("Closed")
```

</details>

#### Wontfix roundtrips through string

- Wontfix roundtrips through string
   - Expected: status_to_string(back) equals `Wontfix`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Wontfix roundtrips through string")
val s = status_to_string(BugStatus.Wontfix)
val back = parse_status(s)
expect(status_to_string(back)).to_equal("Wontfix")
```

</details>

### cross-function interaction

#### severity strings are distinct

- severity strings are distinct
   - Expected: all_different is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("severity strings are distinct")
val s0 = severity_to_string(BugSeverity.P0)
val s1 = severity_to_string(BugSeverity.P1)
val s2 = severity_to_string(BugSeverity.P2)
val s3 = severity_to_string(BugSeverity.P3)
val si = severity_to_string(BugSeverity.Important)
val all_different = s0 != s1 and s1 != s2 and s2 != s3 and s3 != si
expect(all_different).to_equal(true)
```

</details>

#### status strings are distinct

- status strings are distinct
   - Expected: all_distinct is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("status strings are distinct")
val s_open = status_to_string(BugStatus.Open)
val s_inv = status_to_string(BugStatus.Investigating)
val s_conf = status_to_string(BugStatus.Confirmed)
val s_fix = status_to_string(BugStatus.Fixed)
val s_close = status_to_string(BugStatus.Closed)
val s_wont = status_to_string(BugStatus.Wontfix)
val d1 = s_open != s_inv and s_inv != s_conf
val d2 = s_conf != s_fix and s_fix != s_close
val d3 = s_close != s_wont
val all_distinct = d1 and d2 and d3
expect(all_distinct).to_equal(true)
```

</details>

#### severity and status strings do not overlap

- severity and status strings do not overlap
   - Expected: different is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("severity and status strings do not overlap")
val sev_str = severity_to_string(BugSeverity.P0)
val stat_str = status_to_string(BugStatus.Open)
val different = sev_str != stat_str
expect(different).to_equal(true)
```

</details>

#### parse_severity does not interfere with parse_status

- parse_severity does not interfere with parse_status
   - Expected: severity_to_string(sev) equals `P3`
   - Expected: status_to_string(stat) equals `Open`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parse_severity does not interfere with parse_status")
val sev = parse_severity("Open")
val stat = parse_status("P0")
# "Open" is unknown severity -> defaults to P3
expect(severity_to_string(sev)).to_equal("P3")
# "P0" is unknown status -> defaults to Open
expect(status_to_string(stat)).to_equal("Open")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/bug_severity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering severity_to_string, parse_severity, severity roundtrip, status_to_string, parse_status, status roundtrip, cross-function interaction.
- severity_to_string
- parse_severity
- severity roundtrip
- status_to_string
- parse_status
- status roundtrip
- cross-function interaction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
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

- Canonical SPipe generation for source `0463c73601ee645d2dec3a43bccba723ec0fd7ef22bac3c3f5e1bc34cefbfa70`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0463c73601ee645d2dec3a43bccba723ec0fd7ef22bac3c3f5e1bc34cefbfa70`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0463c73601ee645d2dec3a43bccba723ec0fd7ef22bac3c3f5e1bc34cefbfa70`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/database/bug_severity_spec.spl
mirror: doc/06_spec/01_unit/lib/database/bug_severity_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/database/bug_severity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/database/bug_severity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/database/bug_severity_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts P0 to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/database/bug_severity_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts P1 to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/database/bug_severity_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts P2 to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
