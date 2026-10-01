# Compositor Frame Specification

> Tests covering CompositorFrame::empty, CompositorFrame with passes, FrameMetadata, RenderPass::new.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compositor Frame Specification

## Scenarios

### CompositorFrame::empty

#### empty frame has 0 passes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- empty frame has 0 passes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty frame has 0 passes")
val f = CompositorFrame.empty()
expect f.render_pass_list.len() to_equal 0
```

</details>

#### empty frame total_quad_count is 0

- empty frame total_quad_count is 0


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty frame total_quad_count is 0")
val f = CompositorFrame.empty()
expect f.total_quad_count() to_equal 0
```

</details>

#### empty frame root_render_pass_id is -1

- empty frame root_render_pass_id is -1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty frame root_render_pass_id is -1")
val f = CompositorFrame.empty()
expect f.root_render_pass_id() to_equal -1
```

</details>

### CompositorFrame with passes

#### adding one RenderPass bumps pass count

- adding one RenderPass bumps pass count


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adding one RenderPass bumps pass count")
var f = CompositorFrame.empty()
val rp = RenderPass.new(1, _rect(0.0, 0.0, 800.0, 600.0))
f.render_pass_list = f.render_pass_list + [rp]
expect f.render_pass_list.len() to_equal 1
```

</details>

#### root_render_pass_id returns last pass id

- root_render_pass_id returns last pass id


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("root_render_pass_id returns last pass id")
var f = CompositorFrame.empty()
val rp1 = RenderPass.new(10, _rect(0.0, 0.0, 800.0, 600.0))
val rp2 = RenderPass.new(20, _rect(0.0, 0.0, 800.0, 600.0))
f.render_pass_list = f.render_pass_list + [rp1, rp2]
expect f.root_render_pass_id() to_equal 20
```

</details>

#### total_quad_count sums across multiple passes

- total_quad_count sums across multiple passes


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("total_quad_count sums across multiple passes")
var f = CompositorFrame.empty()
var rp1 = RenderPass.new(1, _rect(0.0, 0.0, 100.0, 100.0))
var rp2 = RenderPass.new(2, _rect(0.0, 0.0, 100.0, 100.0))
val color = SkColor4f(r: 1.0, g: 0.0, b: 0.0, a: 1.0)
val q = DrawQuad.solid_color(0, _rect(0.0, 0.0, 50.0, 50.0), color)
rp1.add_quad(q)
rp1.add_quad(q)
rp2.add_quad(q)
f.render_pass_list = f.render_pass_list + [rp1, rp2]
expect f.total_quad_count() to_equal 3
```

</details>

### FrameMetadata

#### fields round-trip through constructor

- fields round-trip through constructor


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fields round-trip through constructor")
val meta = FrameMetadata(
    device_scale_factor: 2.0,
    root_scroll_offset_x: 10.5,
    root_scroll_offset_y: 20.0,
    frame_token: 7
)
expect meta.device_scale_factor to_equal 2.0
expect meta.frame_token to_equal 7
```

</details>

### RenderPass::new

#### new(42, rect) has id=42

- new(42, rect) has id=42


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new(42, rect) has id=42")
val rp = RenderPass.new(42, _rect(0.0, 0.0, 100.0, 100.0))
expect rp.id to_equal 42
```

</details>

#### new pass starts with 0 quads

- new pass starts with 0 quads


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new pass starts with 0 quads")
val rp = RenderPass.new(1, _rect(0.0, 0.0, 100.0, 100.0))
expect rp.quad_count() to_equal 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/viz/compositor_frame_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CompositorFrame::empty, CompositorFrame with passes, FrameMetadata, RenderPass::new.
- CompositorFrame::empty
- CompositorFrame with passes
- FrameMetadata
- RenderPass::new

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `455c97b614d1d8fb50204b444f555d4bc89f034ca2d707c6ab7cfe8e87ea382b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `455c97b614d1d8fb50204b444f555d4bc89f034ca2d707c6ab7cfe8e87ea382b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `455c97b614d1d8fb50204b444f555d4bc89f034ca2d707c6ab7cfe8e87ea382b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/viz/compositor_frame_spec.spl
mirror: doc/06_spec/unit/lib/viz/compositor_frame_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/viz/compositor_frame_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/viz/compositor_frame_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/viz/compositor_frame_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty frame has 0 passes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/viz/compositor_frame_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty frame total_quad_count is 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/viz/compositor_frame_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'empty frame root_render_pass_id is -1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
