# Click Event Specification

> Tests covering ink ClickEvent.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Click Event Specification

## Scenarios

### ink ClickEvent

#### records absolute cell coordinates from the constructor

- records absolute cell coordinates from the constructor
   - Expected: e.col equals `12`
   - Expected: e.row equals `4`
   - Expected: e.localCol equals `0`
   - Expected: e.localRow equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records absolute cell coordinates from the constructor")
val e = ClickEvent.new(12, 4, false)
expect(e.col).to_equal(12)
expect(e.row).to_equal(4)
expect(e.localCol).to_equal(0)
expect(e.localRow).to_equal(0)
```

</details>

#### derives local coordinates relative to a box origin

- derives local coordinates relative to a box origin
   - Expected: e.localCol equals `2`
   - Expected: e.localRow equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("derives local coordinates relative to a box origin")
var e = ClickEvent.new(12, 4, false)
e.setLocalFromBox(10, 3)
expect(e.localCol).to_equal(2)
expect(e.localRow).to_equal(1)
```

</details>

#### allows local coordinates to be set directly

- allows local coordinates to be set directly
   - Expected: e.localCol equals `7`
   - Expected: e.localRow equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("allows local coordinates to be set directly")
var e = ClickEvent.new(1, 1, false)
e.setLocal(7, 9)
expect(e.localCol).to_equal(7)
expect(e.localRow).to_equal(9)
```

</details>

#### reports blank-cell clicks from the constructor flag

- reports blank-cell clicks from the constructor flag
   - Expected: ClickEvent.new(0, 0, true).isBlankCellClick() is true
   - Expected: ClickEvent.new(0, 0, false).isBlankCellClick() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("reports blank-cell clicks from the constructor flag")
expect(ClickEvent.new(0, 0, true).isBlankCellClick()).to_equal(true)
expect(ClickEvent.new(0, 0, false).isBlankCellClick()).to_equal(false)
```

</details>

#### latches immediate-propagation stop only after it is requested

- latches immediate-propagation stop only after it is requested
   - Expected: e.didStopImmediatePropagation() is false
   - Expected: e.didStopImmediatePropagation() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("latches immediate-propagation stop only after it is requested")
var e = clickEventNew(3, 5, false)
expect(e.didStopImmediatePropagation()).to_equal(false)
e.stopImmediatePropagation()
expect(e.didStopImmediatePropagation()).to_equal(true)
```

</details>

#### formats position as col,row

- formats position as col,row
   - Expected: ClickEvent.new(12, 4, false).positionText() equals `12,4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("formats position as col,row")
expect(ClickEvent.new(12, 4, false).positionText()).to_equal("12,4")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/claude_full/ink/events/click_event_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ink ClickEvent.
- ink ClickEvent

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `eb583b09e247b484424df046a0fdfebd9d99313d2d6af7b953b11349606748d1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eb583b09e247b484424df046a0fdfebd9d99313d2d6af7b953b11349606748d1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eb583b09e247b484424df046a0fdfebd9d99313d2d6af7b953b11349606748d1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/01_unit/app/llm_caret/claude_full/ink/events/click_event_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/claude_full/ink/events/click_event_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/claude_full/ink/events/click_event_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/claude_full/ink/events/click_event_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/claude_full/ink/events/click_event_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/app/llm_caret/claude_full/ink/events/click_event_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/claude_full/ink/events/click_event_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records absolute cell coordinates from the constructor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/claude_full/ink/events/click_event_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives local coordinates relative to a box origin' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/claude_full/ink/events/click_event_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows local coordinates to be set directly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
