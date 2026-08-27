# Tui Widget Numeric Guard Specification

> Tests covering tui widget numeric guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tui Widget Numeric Guard Specification

## Scenarios

### tui widget numeric guards

#### guards widget property integer parsing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- guards widget property integer parsing
   - Expected: source does not contain `sel_str.to_int()`
   - Expected: source does not contain `active_idx_str.to_int()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("guards widget property integer parsing")
val source = rt_file_read_text("src/app/ui.render/_TuiWidgets/core_widgets.spl") ?? ""

expect(source).to_contain("fn tui_int_or(value: text, default_value: i64) -> i64")
expect(source).to_contain("tui_int_or(sel_str, -1)")
expect(source).to_contain("tui_int_or(value_str, 0)")
expect(source).to_contain("tui_int_or(active_idx_str, 0)")
expect(source).to_contain("tui_int_or(offset_str, 0)")
expect(source).to_contain("trimmed.to_int() ?? default_value")
expect(source.contains("sel_str.to_int()")).to_equal(false)
expect(source.contains("active_idx_str.to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/tui_widget_numeric_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering tui widget numeric guards.
- tui widget numeric guards

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c3e6a6b038b00860e0b3600e23961756f6815c5026e5c125443cbb950e1bc2e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c3e6a6b038b00860e0b3600e23961756f6815c5026e5c125443cbb950e1bc2e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c3e6a6b038b00860e0b3600e23961756f6815c5026e5c125443cbb950e1bc2e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/ui/tui_widget_numeric_guard_spec.spl
mirror: doc/06_spec/01_unit/app/ui/tui_widget_numeric_guard_spec.md (current)
findings: 5 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/01_unit/app/ui/tui_widget_numeric_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui/tui_widget_numeric_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui/tui_widget_numeric_guard_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/ui/tui_widget_numeric_guard_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/ui/tui_widget_numeric_guard_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards widget property integer parsing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
