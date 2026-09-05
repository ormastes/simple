# Scrollbar Wpt Specification

> Tests covering WPT-derived CSS scrollbar subset.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scrollbar Wpt Specification

## Scenarios

### WPT-derived CSS scrollbar subset

#### CSS scrollbar pure function coverage

#### scrollbar renders track when content overflows

- scrollbar renders track when content overflows
   - Expected: cmds.len() >= 1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("scrollbar renders track when content overflows")
val cmds = paint_scrollbar(0.0, 0.0, 200.0, 400.0, 800.0, 0.0)
expect(cmds.len() >= 1).to_equal(true)
```

</details>

#### scrollbar thumb proportional to viewport content ratio

- scrollbar thumb proportional to viewport content ratio
   - Expected: cmds.len() >= 2 is true
   - Expected: approx_i32(thumb.height, 200) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("scrollbar thumb proportional to viewport content ratio")
# height=400, content_height=800, ratio=0.5, thumb_h = 400 * 0.5 = 200 (above 16 floor)
val cmds = paint_scrollbar(0.0, 0.0, 200.0, 400.0, 800.0, 0.0)
expect(cmds.len() >= 2).to_equal(true)
val thumb = cmds[1]
expect(approx_i32(thumb.height, 200)).to_equal(true)
```

</details>

#### no thumb when content fits within viewport

- no thumb when content fits within viewport
   - Expected: cmds.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("no thumb when content fits within viewport")
# content_height <= height, so only the track command is generated
val cmds = paint_scrollbar(0.0, 0.0, 200.0, 400.0, 300.0, 0.0)
expect(cmds.len()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/feature/web_platform/css/scrollbar_wpt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WPT-derived CSS scrollbar subset.
- WPT-derived CSS scrollbar subset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ce167836274121da98f42448a3205407eabc60bf34000ed46278761acccf5118`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ce167836274121da98f42448a3205407eabc60bf34000ed46278761acccf5118`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ce167836274121da98f42448a3205407eabc60bf34000ed46278761acccf5118`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/feature/web_platform/css/scrollbar_wpt_spec.spl
mirror: doc/06_spec/feature/web_platform/css/scrollbar_wpt_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/web_platform/css/scrollbar_wpt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/web_platform/css/scrollbar_wpt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/web_platform/css/scrollbar_wpt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/web_platform/css/scrollbar_wpt_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scrollbar renders track when content overflows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/scrollbar_wpt_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scrollbar thumb proportional to viewport content ratio' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/web_platform/css/scrollbar_wpt_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'no thumb when content fits within viewport' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
