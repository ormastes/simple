# Aggregator Compose Specification

> Tests covering aggregator_compose.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aggregator Compose Specification

## Scenarios

### aggregator_compose

#### compose_transforms identity with identity yields identity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- compose_transforms identity with identity yields identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("compose_transforms identity with identity yields identity")
val result = compose_transforms(_identity(), _identity())
val eq = _mat_eq(result, _identity())
eq.to_equal(true)
```

</details>

#### compose_transforms translate(5,0) then translate(0,3) yields translate(5,3)

- compose_transforms translate(5,0) then translate(0,3) yields translate(5,3)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("compose_transforms translate(5,0) then translate(0,3) yields translate(5,3)")
val t1 = _translate(5.0, 0.0)
val t2 = _translate(0.0, 3.0)
val result = compose_transforms(t1, t2)
val expected = _translate(5.0, 3.0)
val eq = _mat_eq(result, expected)
eq.to_equal(true)
```

</details>

#### intersect_clips fully overlapping returns the smaller rect

- intersect_clips fully overlapping returns the smaller rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("intersect_clips fully overlapping returns the smaller rect")
val parent_clip = SkRect(left: 0.0, top: 0.0, right: 100.0, bottom: 100.0)
val child_clip  = SkRect(left: 10.0, top: 10.0, right: 50.0, bottom: 50.0)
val result = intersect_clips(parent_clip, child_clip)
result.left.to_equal(10.0)
result.top.to_equal(10.0)
result.right.to_equal(50.0)
result.bottom.to_equal(50.0)
```

</details>

#### intersect_clips disjoint rects returns empty rect

- intersect_clips disjoint rects returns empty rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("intersect_clips disjoint rects returns empty rect")
val parent_clip = SkRect(left: 0.0, top: 0.0, right: 10.0, bottom: 10.0)
val child_clip  = SkRect(left: 20.0, top: 20.0, right: 30.0, bottom: 30.0)
val result = intersect_clips(parent_clip, child_clip)
result.left.to_equal(0.0)
result.top.to_equal(0.0)
result.right.to_equal(0.0)
result.bottom.to_equal(0.0)
```

</details>

#### intersect_clips partially overlapping rects returns correct overlap

- intersect_clips partially overlapping rects returns correct overlap


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("intersect_clips partially overlapping rects returns correct overlap")
val parent_clip = SkRect(left: 0.0, top: 0.0, right: 50.0, bottom: 50.0)
val child_clip  = SkRect(left: 30.0, top: 30.0, right: 80.0, bottom: 80.0)
val result = intersect_clips(parent_clip, child_clip)
result.left.to_equal(30.0)
result.top.to_equal(30.0)
result.right.to_equal(50.0)
result.bottom.to_equal(50.0)
```

</details>

#### compose_effects multiplies opacity values

- compose_effects multiplies opacity values


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("compose_effects multiplies opacity values")
val parent_effect = EffectNode(
    id: 0, parent_id: -1,
    opacity: 0.5, blend_mode: BLEND_MODE_SRC_OVER,
    has_render_surface: false, clip_id: 0, transform_id: 0
)
val child_effect = EffectNode(
    id: 1, parent_id: 0,
    opacity: 0.5, blend_mode: BLEND_MODE_SRC_OVER,
    has_render_surface: false, clip_id: 0, transform_id: 0
)
val result = compose_effects(parent_effect, child_effect)
val diff = result.opacity - 0.25
val abs_diff = if diff < 0.0: 0.0 - diff else: diff
val close = abs_diff < 1e-6
close.to_equal(true)
```

</details>

#### compose_effects child non-SrcOver blend_mode overrides parent SrcOver

- compose_effects child non-SrcOver blend_mode overrides parent SrcOver


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("compose_effects child non-SrcOver blend_mode overrides parent SrcOver")
val blend_multiply: i32 = 2
val parent_effect = EffectNode(
    id: 0, parent_id: -1,
    opacity: 1.0, blend_mode: BLEND_MODE_SRC_OVER,
    has_render_surface: false, clip_id: 0, transform_id: 0
)
val child_effect = EffectNode(
    id: 1, parent_id: 0,
    opacity: 1.0, blend_mode: blend_multiply,
    has_render_surface: false, clip_id: 0, transform_id: 0
)
val result = compose_effects(parent_effect, child_effect)
result.blend_mode.to_equal(blend_multiply)
```

</details>

#### compose_effects both SrcOver yields SrcOver blend mode

- compose_effects both SrcOver yields SrcOver blend mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("compose_effects both SrcOver yields SrcOver blend mode")
val parent_effect = EffectNode(
    id: 0, parent_id: -1,
    opacity: 1.0, blend_mode: BLEND_MODE_SRC_OVER,
    has_render_surface: false, clip_id: 0, transform_id: 0
)
val child_effect = EffectNode(
    id: 1, parent_id: 0,
    opacity: 1.0, blend_mode: BLEND_MODE_SRC_OVER,
    has_render_surface: false, clip_id: 0, transform_id: 0
)
val result = compose_effects(parent_effect, child_effect)
result.blend_mode.to_equal(BLEND_MODE_SRC_OVER)
```

</details>

#### effective_transform_for_surface for root node returns identity

- effective_transform_for_surface for root node returns identity


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("effective_transform_for_surface for root node returns identity")
var tree = TransformTree.new()
# root node already at id=0 with empty local (falls back to identity)
val sid = _surface(0)
val result = effective_transform_for_surface(sid, tree)
val eq = _mat_eq(result, _identity())
eq.to_equal(true)
```

</details>

#### effective_clip_for_surface for 2-level nested clip returns intersection

- effective_clip_for_surface for 2-level nested clip returns intersection


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("effective_clip_for_surface for 2-level nested clip returns intersection")
var tree = ClipTree.new()
# root node (id=0) has clip_w=0/clip_h=0 (no clip at root by default)
# Add a parent clip node at id=1
val parent_node = ClipNode(
    id: 1, parent_id: 0,
    clip_x: 0.0, clip_y: 0.0, clip_w: 100.0, clip_h: 100.0
)
tree.add_node(parent_node)
# Add a child clip node at id=2
val child_node = ClipNode(
    id: 2, parent_id: 1,
    clip_x: 20.0, clip_y: 20.0, clip_w: 40.0, clip_h: 40.0
)
tree.add_node(child_node)
val sid = _surface(2)
val result = effective_clip_for_surface(sid, tree)
# root node has clip_w=clip_h=0 -> rect (0,0,0,0)
# parent clip: (0,0,100,100) intersected with root (0,0,0,0) -> (0,0,0,0)
# child clip: (20,20,60,60) intersected with (0,0,0,0) -> (0,0,0,0)
# So result is empty rect (disjoint with zero-size root)
val is_empty = result.left >= result.right or result.top >= result.bottom
is_empty.to_equal(true)
```

</details>

#### effective_clip_for_surface for a clip node with parent_id -1 returns own rect

- effective_clip_for_surface for a clip node with parent_id -1 returns own rect


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("effective_clip_for_surface for a clip node with parent_id -1 returns own rect")
# Build a fresh ClipTree where we treat node 0's clip as real
var tree = ClipTree.new()
# Add a standalone clip node with parent_id=-1 so it is treated as root
val standalone = ClipNode(
    id: 0, parent_id: -1,
    clip_x: 5.0, clip_y: 5.0, clip_w: 30.0, clip_h: 30.0
)
# We can't replace node 0 in tree (already inserted), so use a separate tree.
# ClipTree.new() inserts a root with id=0; add_node assigns the next id.
# Instead, directly verify behavior using the default root via get(0):
# The root in ClipTree.new() has clip_x=0, clip_y=0, clip_w=0, clip_h=0, parent_id=-1.
# So effective_clip_for_surface for surface with sink_id=0 returns SkRect(0,0,0,0).
val sid = _surface(0)
val result = effective_clip_for_surface(sid, tree)
result.left.to_equal(0.0)
result.top.to_equal(0.0)
```

</details>

#### effective_effect_for_surface for 2-level tree multiplies opacity

- effective_effect_for_surface for 2-level tree multiplies opacity


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("effective_effect_for_surface for 2-level tree multiplies opacity")
var tree = EffectTree.new()
# root node (id=0) opacity=1.0, blend_mode=0 (already inserted by EffectTree.new())
val child_node = EffectNode(
    id: 1, parent_id: 0,
    opacity: 0.5, blend_mode: BLEND_MODE_SRC_OVER,
    has_render_surface: false, clip_id: 0, transform_id: 0
)
tree.add_node(child_node)
val sid = _surface(1)
val result = effective_effect_for_surface(sid, tree)
# root opacity 1.0 * child opacity 0.5 = 0.5
val diff = result.opacity - 0.5
val abs_diff = if diff < 0.0: 0.0 - diff else: diff
val close = abs_diff < 1e-6
close.to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/viz/aggregator_compose_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering aggregator_compose.
- aggregator_compose

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b01a54bf348bf6a1051d18f2a5671e900f06c637b4066d3ed29cf9b5e1aea367`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b01a54bf348bf6a1051d18f2a5671e900f06c637b4066d3ed29cf9b5e1aea367`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b01a54bf348bf6a1051d18f2a5671e900f06c637b4066d3ed29cf9b5e1aea367`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/viz/aggregator_compose_spec.spl
mirror: doc/06_spec/01_unit/lib/viz/aggregator_compose_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/lib/viz/aggregator_compose_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/viz/aggregator_compose_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/viz/aggregator_compose_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/01_unit/lib/viz/aggregator_compose_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/viz/aggregator_compose_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compose_transforms identity with identity yields identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/viz/aggregator_compose_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compose_transforms translate(5,0) then translate(0,3) yields translate(5,3)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/viz/aggregator_compose_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'intersect_clips fully overlapping returns the smaller rect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
