# Split Pane Specification

> Tests covering SplitPaneLayout.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Split Pane Specification

## Scenarios

### SplitPaneLayout

#### creates layout with single root pane

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates layout with single root pane


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates layout with single root pane")
val layout = split_pane_create()
val panes = split_pane_list_panes(layout)
val count = panes.len()
expect count to_equal(1)
```

</details>

#### splits pane horizontally

- splits pane horizontally


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits pane horizontally")
val layout = split_pane_create()
val new_id = split_pane_split(layout, SplitDirection.Horizontal)
val panes = split_pane_list_panes(layout)
val count = panes.len()
expect count to_equal(2)
```

</details>

#### splits pane vertically

- splits pane vertically


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("splits pane vertically")
val layout = split_pane_create()
val new_id = split_pane_split(layout, SplitDirection.Vertical)
val panes = split_pane_list_panes(layout)
val count = panes.len()
expect count to_equal(2)
```

</details>

#### focus changes active pane

- focus changes active pane


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("focus changes active pane")
val layout = split_pane_create()
val panes_before = split_pane_list_panes(layout)
val first_id = panes_before[0]
split_pane_split(layout, SplitDirection.Horizontal)
split_pane_focus(layout, first_id)
val active = split_pane_active(layout)
expect active to_equal(first_id)
```

</details>

#### lists panes correctly after two splits

- lists panes correctly after two splits


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists panes correctly after two splits")
val layout = split_pane_create()
split_pane_split(layout, SplitDirection.Horizontal)
split_pane_split(layout, SplitDirection.Vertical)
val panes = split_pane_list_panes(layout)
val count = panes.len()
expect count to_equal(3)
```

</details>

#### close pane returns to single

- close pane returns to single


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("close pane returns to single")
val layout = split_pane_create()
val new_id = split_pane_split(layout, SplitDirection.Horizontal)
split_pane_close(layout, new_id)
val panes = split_pane_list_panes(layout)
val count = panes.len()
expect count to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/split_pane_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SplitPaneLayout.
- SplitPaneLayout

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

- Canonical SPipe generation for source `61889e4e301b888932adea07f022ff7bf743e148ec435e6505e4e286c5432f38`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `61889e4e301b888932adea07f022ff7bf743e148ec435e6505e4e286c5432f38`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `61889e4e301b888932adea07f022ff7bf743e148ec435e6505e4e286c5432f38`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/editor/split_pane_spec.spl
mirror: doc/06_spec/01_unit/lib/editor/split_pane_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/editor/split_pane_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/editor/split_pane_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/editor/split_pane_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates layout with single root pane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/split_pane_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'splits pane horizontally' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/editor/split_pane_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'splits pane vertically' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
