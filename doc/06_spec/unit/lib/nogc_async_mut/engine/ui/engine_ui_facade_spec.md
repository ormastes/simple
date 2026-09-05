# Engine Ui Facade Specification

> Tests covering nogc_async_mut engine ui facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Ui Facade Specification

## Scenarios

### nogc_async_mut engine ui facade

#### re-exports canvas layout and element mutation helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports canvas layout and element mutation helpers
   - Expected: canvas.element_count() equals `2`
   - Expected: canvas.find_by_name("title") equals `label_idx`
   - Expected: canvas.set_parent(label_idx, panel_idx) is true
   - Expected: canvas.set_content(label_idx, "World") is true
   - Expected: canvas.set_visible(panel_idx, false) is true
   - Expected: canvas.get_visible_elements().length() equals `1`
   - Expected: rect.x equals `10.0`
   - Expected: rect.y equals `20.0`
   - Expected: rect.contains_point(20.0, 25.0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports canvas layout and element mutation helpers")
var canvas = UICanvas.new(800.0, 600.0, "screen")
val panel = UIElement.new("panel", "panel", 200.0, 100.0)
val panel_idx = canvas.add_element(panel)
val label_idx = canvas.add_element(create_label("title", "Hello", 10.0, 20.0, 120.0, 30.0))

expect(canvas.element_count()).to_equal(2)
expect(canvas.find_by_name("title")).to_equal(label_idx)
expect(canvas.set_parent(label_idx, panel_idx)).to_equal(true)
expect(canvas.set_content(label_idx, "World")).to_equal(true)
expect(canvas.set_visible(panel_idx, false)).to_equal(true)
expect(canvas.get_visible_elements().length()).to_equal(1)

val rect = canvas.compute_rect(label_idx)
expect(rect.x).to_equal(10.0)
expect(rect.y).to_equal(20.0)
expect(rect.contains_point(20.0, 25.0)).to_equal(true)
```

</details>

#### re-exports common widget constructors and anchors

- re-exports common widget constructors and anchors
   - Expected: center.min_x equals `0.5`
   - Expected: button.element_type equals `button`
   - Expected: progress.content equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports common widget constructors and anchors")
val center = Anchor.center()
expect(center.min_x).to_equal(0.5)
val button = create_button("ok", "OK", 1.0, 2.0, 80.0, 24.0)
expect(button.element_type).to_equal("button")
val progress = create_progress_bar("load", 0.0, 0.0, 100.0, 12.0)
expect(progress.content).to_equal("0")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/engine/ui/engine_ui_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut engine ui facade.
- nogc_async_mut engine ui facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `cc2614a8c78c70ae629897253da436d8ce1eaf7c4c484847406dc6edefcf2228`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cc2614a8c78c70ae629897253da436d8ce1eaf7c4c484847406dc6edefcf2228`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cc2614a8c78c70ae629897253da436d8ce1eaf7c4c484847406dc6edefcf2228`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/nogc_async_mut/engine/ui/engine_ui_facade_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/engine/ui/engine_ui_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/engine/ui/engine_ui_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/engine/ui/engine_ui_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/engine/ui/engine_ui_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/engine/ui/engine_ui_facade_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports canvas layout and element mutation helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/engine/ui/engine_ui_facade_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports common widget constructors and anchors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
