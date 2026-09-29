# Gui Component State Specification

> Tests covering tiny GUI component metadata and bounded state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gui Component State Specification

## Scenarios

### tiny GUI component metadata and bounded state

#### exposes the base component metadata and rejects unknown IDs

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### adds nodes within capacity and rejects overflow and stale parents

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = TinyGuiState.bounded(2)
val root = state.add(TinyHandle.invalid(), TINY_COMPONENT_PANE, TinyRect(x: 0, y: 0, width: 100, height: 50), "")
expect(root.is_ok()).to_be(true)
val child = state.add(state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 2, y: 2, width: 20, height: 8), "hello")
expect(child.is_ok()).to_be(true)
expect(state.add(TinyHandle.invalid(), TINY_COMPONENT_TEXT, TinyRect.empty(), "").is_ok()).to_be(false)

var other = TinyGuiState.bounded(2)
val stale = TinyHandle(index: 0, generation: 99)
expect(other.add(stale, TINY_COMPONENT_TEXT, TinyRect.empty(), "").is_ok()).to_be(false)
expect(other.add(TinyHandle.invalid(), TINY_COMPONENT_TEXT, TinyRect(x: 0, y: 0, width: -1, height: 1), "").is_ok()).to_be(false)
```

</details>

#### cycles focus over focusable controls only

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = TinyGuiState.bounded(4)
state.add(TinyHandle.invalid(), TINY_COMPONENT_TEXT, TinyRect.empty(), "label")
state.add(TinyHandle.invalid(), TINY_COMPONENT_BUTTON, TinyRect.empty(), "go")
state.add(TinyHandle.invalid(), TINY_COMPONENT_CHECKBOX, TinyRect.empty(), "check")
expect(state.focus_next().is_ok()).to_be(true)
expect(state.focused_index).to_equal(1)
expect(state.focus_next().is_ok()).to_be(true)
expect(state.focused_index).to_equal(2)

var empty = TinyGuiState.bounded(0)
expect(empty.focus_next().is_ok()).to_be(false)
```

</details>

#### lays out Row Column and Stack children through the shared pane invariant

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = TinyGuiState.bounded(9)
state.add(TinyHandle.invalid(), TINY_COMPONENT_ROW, TinyRect(x: 0, y: 0, width: 30, height: 3), "")
state.add(state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 9, y: 9, width: 5, height: 1), "a")
state.add(state.handle_at(0), TINY_COMPONENT_TEXT, TinyRect(x: 9, y: 9, width: 6, height: 1), "b")
state.add(TinyHandle.invalid(), TINY_COMPONENT_COLUMN, TinyRect(x: 0, y: 5, width: 30, height: 3), "")
state.add(state.handle_at(3), TINY_COMPONENT_TEXT, TinyRect(x: 7, y: 7, width: 5, height: 1), "c")
state.add(state.handle_at(3), TINY_COMPONENT_TEXT, TinyRect(x: 7, y: 7, width: 5, height: 2), "d")
state.add(TinyHandle.invalid(), TINY_COMPONENT_STACK, TinyRect(x: 0, y: 10, width: 30, height: 4), "")
state.add(state.handle_at(6), TINY_COMPONENT_TEXT, TinyRect(x: 2, y: 1, width: 5, height: 1), "under")
state.add(state.handle_at(6), TINY_COMPONENT_TEXT, TinyRect(x: 2, y: 1, width: 5, height: 1), "over")
val panes = state.resolved_panes(TinyRect(x: 0, y: 0, width: 40, height: 20))
expect(panes[1].absolute.x).to_equal(0)
expect(panes[2].absolute.x).to_equal(5)
expect(panes[4].absolute.y).to_equal(5)
expect(panes[5].absolute.y).to_equal(6)
expect(panes[7].absolute.x).to_equal(panes[8].absolute.x)
expect(panes[7].absolute.y).to_equal(panes[8].absolute.y)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/tiny/gui_component_state_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering tiny GUI component metadata and bounded state.
- tiny GUI component metadata and bounded state

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

- Canonical SPipe generation for source `24b296c4aa2457c4b164c9422385096bca350414b0b296e1576e3bade4c3a1ab`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `24b296c4aa2457c4b164c9422385096bca350414b0b296e1576e3bade4c3a1ab`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `24b296c4aa2457c4b164c9422385096bca350414b0b296e1576e3bade4c3a1ab`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/01_unit/lib/tiny/gui_component_state_spec.spl
mirror: doc/06_spec/01_unit/lib/tiny/gui_component_state_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/tiny/gui_component_state_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/tiny/gui_component_state_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/tiny/gui_component_state_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/tiny/gui_component_state_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/tiny/gui_component_state_spec.spl:15:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'exposes the base component metadata and rejects unknown IDs' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/gui_component_state_spec.spl:25:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'adds nodes within capacity and rejects overflow and stale parents' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/gui_component_state_spec.spl:38:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'cycles focus over focusable controls only' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/tiny/gui_component_state_spec.spl:51:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'lays out Row Column and Stack children through the shared pane invariant' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
