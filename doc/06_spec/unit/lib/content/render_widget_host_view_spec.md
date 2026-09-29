# Render Widget Host View Specification

> Tests covering RenderWidgetHostView.new, RenderWidgetHostView input.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Render Widget Host View Specification

## Scenarios

### RenderWidgetHostView.new

#### new RWHV has 0 pending inputs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- new RWHV has 0 pending inputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new RWHV has 0 pending inputs")
val rwhv = RenderWidgetHostView.new(_surface_id(), _rect(), _dc())
expect rwhv.pending_input_count() to_equal 0
```

</details>

#### bounds round-trip

- bounds round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bounds round-trip")
val bounds = SkRect(left: 10.0, top: 20.0, right: 500.0, bottom: 400.0)
val rwhv = RenderWidgetHostView.new(_surface_id(), bounds, _dc())
expect rwhv.bounds.left to_equal 10.0
```

</details>

### RenderWidgetHostView input

#### dispatch_input bumps pending count

- dispatch_input bumps pending count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch_input bumps pending count")
var rwhv = RenderWidgetHostView.new(_surface_id(), _rect(), _dc())
val ev = InputEvent(kind: InputEventKind.MouseDown, x: 100, y: 200, data: 0)
rwhv.dispatch_input(ev)
expect rwhv.pending_input_count() to_equal 1
```

</details>

#### submit_compositor_frame returns without error

- submit_compositor_frame returns without error


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("submit_compositor_frame returns without error")
var rwhv = RenderWidgetHostView.new(_surface_id(), _rect(), _dc())
val frame = CompositorFrame.empty()
rwhv.submit_compositor_frame(frame)
expect rwhv.pending_input_count() to_equal 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/content/render_widget_host_view_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RenderWidgetHostView.new, RenderWidgetHostView input.
- RenderWidgetHostView.new
- RenderWidgetHostView input

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

- Canonical SPipe generation for source `b72488f7b9891143c128ddb7ddb9a2645aaeee2551eb1e18e8d7b1bea8e67e1b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b72488f7b9891143c128ddb7ddb9a2645aaeee2551eb1e18e8d7b1bea8e67e1b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b72488f7b9891143c128ddb7ddb9a2645aaeee2551eb1e18e8d7b1bea8e67e1b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/content/render_widget_host_view_spec.spl
mirror: doc/06_spec/unit/lib/content/render_widget_host_view_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/content/render_widget_host_view_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/content/render_widget_host_view_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/content/render_widget_host_view_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'new RWHV has 0 pending inputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/content/render_widget_host_view_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bounds round-trip' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/content/render_widget_host_view_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatch_input bumps pending count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
