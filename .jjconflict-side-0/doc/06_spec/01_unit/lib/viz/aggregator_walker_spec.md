# Aggregator Walker Specification

> <details>

<!-- sdn-diagram:id=aggregator_walker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=aggregator_walker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

aggregator_walker_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=aggregator_walker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Aggregator Walker Specification

## Scenarios

### aggregator_walker

#### walk_referenced_surfaces returns empty list when root has no referenced surfaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = _empty_frame([])
val ctx = _context_with([])
val result = walk_referenced_surfaces(root, ctx)
val result_len = result.len()
result_len.to_equal(0)
```

</details>

#### walk_referenced_surfaces returns one id when root references one child

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val child_sid = _sid(2, 0)
val root = _empty_frame([child_sid])
val child_frame = _empty_frame([])
val ctx = _context_with([_entry(child_sid, child_frame)])
val result = walk_referenced_surfaces(root, ctx)
val result_len = result.len()
result_len.to_equal(1)
val found = result[0]
val eq = found.equals(child_sid)
eq.to_equal(true)
```

</details>

#### walk_referenced_surfaces terminates and dedups on a cycle A to B to A

1.  entry
2.  entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sid_a = _sid(10, 0)
val sid_b = _sid(11, 0)
# A references B, B references A — cycle
val frame_a = _empty_frame([sid_b])
val frame_b = _empty_frame([sid_a])
val root = _empty_frame([sid_a])
val ctx = _context_with([
    _entry(sid_a, frame_a),
    _entry(sid_b, frame_b)
])
val result = walk_referenced_surfaces(root, ctx)
# Should see each of sid_a, sid_b exactly once
val result_len = result.len()
result_len.to_equal(2)
```

</details>

#### find_frame_for returns Some when id is in context

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sid = _sid(1, 0)
val frame = _empty_frame([])
val ctx = _context_with([_entry(sid, frame)])
val maybe = find_frame_for(ctx, sid)
if val Some(f) = maybe:
    val ref_len = f.referenced_surfaces.len()
    ref_len.to_equal(0)
else:
    # force failure: should have found it
    true.to_equal(false)
```

</details>

#### find_frame_for returns None when id is not in context

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify by empty context: find_frame_for on a fresh empty context always returns None.
# Use walk_referenced_surfaces to indirectly confirm: if find_frame_for correctly
# returns None for the unknown_sid, walk won't recurse into it (no child frame).
val unknown_sid = _sid(99, 0)
val ctx = _context_with([])
val root_frame = _empty_frame([unknown_sid])
val result = walk_referenced_surfaces(root_frame, ctx)
# walk adds unknown_sid to result (it's referenced), but since find_frame_for
# returns None there are no children to add. Result length = 1.
val result_len = result.len()
result_len.to_equal(1)
```

</details>

#### inline_render_pass appends child quads to parent quads

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent_sqs = [_sqs()]
val parent_quads = [_solid_quad(0)]
val parent_pass = _pass_with_quads(1, parent_quads, parent_sqs)

val child_sqs = [_sqs(), _sqs()]
val child_quads = [_solid_quad(0), _solid_quad(1), _solid_quad(1)]
val child_frame = _frame_with_one_pass([], 2, child_quads, child_sqs)

val result = inline_render_pass(parent_pass, child_frame)
# parent had 1 quad, child has 3 → merged has 4
val merged_len = result.quads.len()
merged_len.to_equal(4)
```

</details>

#### inline_render_pass remaps child sqs indices by parent sqs count offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parent_sqs = [_sqs(), _sqs()]   # 2 parent sqs → offset = 2
val parent_quads = [_solid_quad(0), _solid_quad(1)]
val parent_pass = _pass_with_quads(1, parent_quads, parent_sqs)

val child_sqs = [_sqs()]
# child quad references sqs index 0 in child's sqs list
val child_quads = [_solid_quad(0)]
val child_frame = _frame_with_one_pass([], 2, child_quads, child_sqs)

val result = inline_render_pass(parent_pass, child_frame)
# The appended (3rd) quad was child quad at sqs index 0, remapped to 0+2=2
val merged_third_quad = result.quads[2]
merged_third_quad.shared_quad_state_index.to_equal(2)
```

</details>

#### drop_missing_surface removes RenderPass quads matching hint and preserves others

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sqs_list = [_sqs()]
# One solid-color quad (not a RenderPass quad) and one RenderPass quad with pass_id=42
val solid = _solid_quad(0)
val rp_quad = _render_pass_quad(0, 42)
val render_pass = _pass_with_quads(1, [solid, rp_quad], sqs_list)

val result = drop_missing_surface(render_pass, "42")
# RenderPass quad with render_pass_id==42 should be dropped; solid kept
val kept_len = result.quads.len()
kept_len.to_equal(1)
val kept = result.quads[0]
val is_solid = if kept.kind == DrawQuadKind.SolidColor: true else: false
is_solid.to_equal(true)
```

</details>

#### drop_missing_surface returns all quads unchanged when no quad matches hint

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sqs_list = [_sqs()]
val solid1 = _solid_quad(0)
val solid2 = _solid_quad(0)
val render_pass = _pass_with_quads(1, [solid1, solid2], sqs_list)

val result = drop_missing_surface(render_pass, "99")
val unchanged_len = result.quads.len()
unchanged_len.to_equal(2)
```

</details>

#### placeholder_deferred_surface returns pass with same quad count

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sqs_list = [_sqs()]
val quads = [_solid_quad(0), _solid_quad(0)]
val render_pass = _pass_with_quads(1, quads, sqs_list)
val sid = _sid(5, 0)

val result = placeholder_deferred_surface(render_pass, sid)
val deferred_len = result.quads.len()
deferred_len.to_equal(2)
result.id.to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/viz/aggregator_walker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- aggregator_walker

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
