# Bug Severity Specification

> <details>

<!-- sdn-diagram:id=bug_severity_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bug_severity_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bug_severity_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bug_severity_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bug Severity Specification

## Scenarios

### severity_to_string

#### converts P0 to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(severity_to_string(BugSeverity.P0)).to_equal("P0")
```

</details>

#### converts P1 to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(severity_to_string(BugSeverity.P1)).to_equal("P1")
```

</details>

#### converts P2 to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(severity_to_string(BugSeverity.P2)).to_equal("P2")
```

</details>

#### converts P3 to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(severity_to_string(BugSeverity.P3)).to_equal("P3")
```

</details>

#### converts Important to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(severity_to_string(BugSeverity.Important)).to_equal("Important")
```

</details>

### parse_severity

#### parses P0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sev = parse_severity("P0")
expect(severity_to_string(sev)).to_equal("P0")
```

</details>

#### parses P1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sev = parse_severity("P1")
expect(severity_to_string(sev)).to_equal("P1")
```

</details>

#### parses P2

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sev = parse_severity("P2")
expect(severity_to_string(sev)).to_equal("P2")
```

</details>

#### parses P3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sev = parse_severity("P3")
expect(severity_to_string(sev)).to_equal("P3")
```

</details>

#### parses Important

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sev = parse_severity("Important")
expect(severity_to_string(sev)).to_equal("Important")
```

</details>

#### defaults to P3 for unknown string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sev = parse_severity("Unknown")
expect(severity_to_string(sev)).to_equal("P3")
```

</details>

#### defaults to P3 for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sev = parse_severity("")
expect(severity_to_string(sev)).to_equal("P3")
```

</details>

#### defaults to P3 for lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sev = parse_severity("p0")
expect(severity_to_string(sev)).to_equal("P3")
```

</details>

#### defaults to P3 for random text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sev = parse_severity("critical")
expect(severity_to_string(sev)).to_equal("P3")
```

</details>

### severity roundtrip

#### P0 roundtrips through string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = severity_to_string(BugSeverity.P0)
val back = parse_severity(s)
expect(severity_to_string(back)).to_equal("P0")
```

</details>

#### P1 roundtrips through string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = severity_to_string(BugSeverity.P1)
val back = parse_severity(s)
expect(severity_to_string(back)).to_equal("P1")
```

</details>

#### P2 roundtrips through string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = severity_to_string(BugSeverity.P2)
val back = parse_severity(s)
expect(severity_to_string(back)).to_equal("P2")
```

</details>

#### P3 roundtrips through string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = severity_to_string(BugSeverity.P3)
val back = parse_severity(s)
expect(severity_to_string(back)).to_equal("P3")
```

</details>

#### Important roundtrips through string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = severity_to_string(BugSeverity.Important)
val back = parse_severity(s)
expect(severity_to_string(back)).to_equal("Important")
```

</details>

### status_to_string

#### converts Open to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(status_to_string(BugStatus.Open)).to_equal("Open")
```

</details>

#### converts Investigating to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(status_to_string(BugStatus.Investigating)).to_equal("Investigating")
```

</details>

#### converts Confirmed to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(status_to_string(BugStatus.Confirmed)).to_equal("Confirmed")
```

</details>

#### converts Fixed to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(status_to_string(BugStatus.Fixed)).to_equal("Fixed")
```

</details>

#### converts Closed to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(status_to_string(BugStatus.Closed)).to_equal("Closed")
```

</details>

#### converts Wontfix to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(status_to_string(BugStatus.Wontfix)).to_equal("Wontfix")
```

</details>

### parse_status

#### parses Open

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val st = parse_status("Open")
expect(status_to_string(st)).to_equal("Open")
```

</details>

#### parses Investigating

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val st = parse_status("Investigating")
expect(status_to_string(st)).to_equal("Investigating")
```

</details>

#### parses Confirmed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val st = parse_status("Confirmed")
expect(status_to_string(st)).to_equal("Confirmed")
```

</details>

#### parses Fixed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val st = parse_status("Fixed")
expect(status_to_string(st)).to_equal("Fixed")
```

</details>

#### parses Closed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val st = parse_status("Closed")
expect(status_to_string(st)).to_equal("Closed")
```

</details>

#### parses Wontfix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val st = parse_status("Wontfix")
expect(status_to_string(st)).to_equal("Wontfix")
```

</details>

#### defaults to Open for unknown string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val st = parse_status("Unknown")
expect(status_to_string(st)).to_equal("Open")
```

</details>

#### defaults to Open for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val st = parse_status("")
expect(status_to_string(st)).to_equal("Open")
```

</details>

#### defaults to Open for lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val st = parse_status("open")
expect(status_to_string(st)).to_equal("Open")
```

</details>

#### defaults to Open for random text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val st = parse_status("resolved")
expect(status_to_string(st)).to_equal("Open")
```

</details>

### status roundtrip

#### Open roundtrips through string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = status_to_string(BugStatus.Open)
val back = parse_status(s)
expect(status_to_string(back)).to_equal("Open")
```

</details>

#### Investigating roundtrips through string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = status_to_string(BugStatus.Investigating)
val back = parse_status(s)
expect(status_to_string(back)).to_equal("Investigating")
```

</details>

#### Confirmed roundtrips through string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = status_to_string(BugStatus.Confirmed)
val back = parse_status(s)
expect(status_to_string(back)).to_equal("Confirmed")
```

</details>

#### Fixed roundtrips through string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = status_to_string(BugStatus.Fixed)
val back = parse_status(s)
expect(status_to_string(back)).to_equal("Fixed")
```

</details>

#### Closed roundtrips through string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = status_to_string(BugStatus.Closed)
val back = parse_status(s)
expect(status_to_string(back)).to_equal("Closed")
```

</details>

#### Wontfix roundtrips through string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = status_to_string(BugStatus.Wontfix)
val back = parse_status(s)
expect(status_to_string(back)).to_equal("Wontfix")
```

</details>

### cross-function interaction

#### severity strings are distinct

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sev_str = severity_to_string(BugSeverity.P0)
val stat_str = status_to_string(BugStatus.Open)
val different = sev_str != stat_str
expect(different).to_equal(true)
```

</details>

#### parse_severity does not interfere with parse_status

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
