# Draw IR incremental patch generation

> Backends normally re-receive a whole `DrawIrComposition` every frame and diff it themselves. This spec covers the incremental patch companion (`common.ui.draw_ir_patch`): computing a compact list of per-component operations (Insert / Remove / UpdateGeometry / UpdateText / UpdateStyle / Reorder) between two composition revisions, and applying that patch back onto the baseline to reproduce the target composition exactly, command-by-command — so a renderer can repaint only the changed regions instead of the whole frame.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw IR incremental patch generation

Backends normally re-receive a whole `DrawIrComposition` every frame and diff it themselves. This spec covers the incremental patch companion (`common.ui.draw_ir_patch`): computing a compact list of per-component operations (Insert / Remove / UpdateGeometry / UpdateText / UpdateStyle / Reorder) between two composition revisions, and applying that patch back onto the baseline to reproduce the target composition exactly, command-by-command — so a renderer can repaint only the changed regions instead of the whole frame.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/draw_ir_patch_spec.spl` |
| Updated | 2026-07-20 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Backends normally re-receive a whole `DrawIrComposition` every frame and
diff it themselves. This spec covers the incremental patch companion
(`common.ui.draw_ir_patch`): computing a compact list of per-component
operations (Insert / Remove / UpdateGeometry / UpdateText / UpdateStyle /
Reorder) between two composition revisions, and applying that patch back
onto the baseline to reproduce the target composition exactly,
command-by-command — so a renderer can repaint only the changed regions
instead of the whole frame.

## Examples

A new sibling component emits an Insert op carrying only `new_bounds`;
removing one emits a Remove op carrying only `old_bounds`. A pure
position/size change emits UpdateGeometry; a text-only or style-only
change emits its own narrow op instead of a blanket replace. A component
that keeps its content but moves emits Reorder — unless content ALSO
changed at the new position, in which case the content-change op wins and
Reorder is suppressed. The round-trip contract holds on every case,
including a ~30-command mixed composition exercising every op kind at
once: `apply(old, patch_between(old, new))` always equals `new`,
command-by-command.

## Scenarios

### Draw IR patch generation

#### emits an Insert op for a new component with new_bounds set and no old_bounds

- draw ir batch
- draw ir rect
- draw ir batch
- draw ir rect
- draw ir rect
   - Expected: _op_kind_present(patch.operations, DRAW_IR_PATCH_OP_INSERT, "fresh") is true
   - Expected: op.old_bounds.present is false
   - Expected: op.new_bounds.present is true
   - Expected: op.new_bounds.x equals `1`
   - Expected: op.new_bounds.y equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline = draw_ir_composition("rev-1", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("box", 10, 10, 50, 20, 1u32)
    ])
])
val current = draw_ir_composition("rev-2", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("box", 10, 10, 50, 20, 1u32),
        draw_ir_rect("fresh", 1, 2, 5, 6, 9u32)
    ])
])
val patch = draw_ir_patch_between(baseline, "rev-1", current, "rev-2")
expect(_op_kind_present(patch.operations, DRAW_IR_PATCH_OP_INSERT, "fresh")).to_equal(true)
for op in patch.operations:
    if op.component_id == "fresh":
        expect(op.old_bounds.present).to_equal(false)
        expect(op.new_bounds.present).to_equal(true)
        expect(op.new_bounds.x).to_equal(1)
        expect(op.new_bounds.y).to_equal(2)
```

</details>

#### emits a Remove op for a dropped component with old_bounds set and no new_bounds

- draw ir batch
- draw ir rect
- draw ir rect
- draw ir batch
- draw ir rect
   - Expected: _op_kind_present(patch.operations, DRAW_IR_PATCH_OP_REMOVE, "gone") is true
   - Expected: op.old_bounds.present is true
   - Expected: op.old_bounds.x equals `90`
   - Expected: op.new_bounds.present is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline = draw_ir_composition("rev-1", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("box", 10, 10, 50, 20, 1u32),
        draw_ir_rect("gone", 90, 91, 10, 11, 3u32)
    ])
])
val current = draw_ir_composition("rev-2", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("box", 10, 10, 50, 20, 1u32)
    ])
])
val patch = draw_ir_patch_between(baseline, "rev-1", current, "rev-2")
expect(_op_kind_present(patch.operations, DRAW_IR_PATCH_OP_REMOVE, "gone")).to_equal(true)
for op in patch.operations:
    if op.component_id == "gone":
        expect(op.old_bounds.present).to_equal(true)
        expect(op.old_bounds.x).to_equal(90)
        expect(op.new_bounds.present).to_equal(false)
```

</details>

#### emits an UpdateGeometry op when x/y/width/height change

- draw ir batch
- draw ir rect
- draw ir batch
- draw ir rect
   - Expected: _op_kind_present(patch.operations, DRAW_IR_PATCH_OP_UPDATE_GEOMETRY, "box") is true
   - Expected: op.old_bounds.x equals `10`
   - Expected: op.new_bounds.x equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline = draw_ir_composition("rev-1", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("box", 10, 10, 50, 20, 1u32)
    ])
])
val current = draw_ir_composition("rev-2", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("box", 30, 40, 55, 25, 1u32)
    ])
])
val patch = draw_ir_patch_between(baseline, "rev-1", current, "rev-2")
expect(_op_kind_present(patch.operations, DRAW_IR_PATCH_OP_UPDATE_GEOMETRY, "box")).to_equal(true)
for op in patch.operations:
    if op.kind == DRAW_IR_PATCH_OP_UPDATE_GEOMETRY:
        expect(op.old_bounds.x).to_equal(10)
        expect(op.new_bounds.x).to_equal(30)
```

</details>

#### emits an UpdateText op when text_value changes

- draw ir batch
- draw ir text
- draw ir batch
- draw ir text
   - Expected: _op_kind_present(patch.operations, DRAW_IR_PATCH_OP_UPDATE_TEXT, "label") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline = draw_ir_composition("rev-1", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_text("label", 5, 5, "Old", 2u32)
    ])
])
val current = draw_ir_composition("rev-2", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_text("label", 5, 5, "New", 2u32)
    ])
])
val patch = draw_ir_patch_between(baseline, "rev-1", current, "rev-2")
expect(_op_kind_present(patch.operations, DRAW_IR_PATCH_OP_UPDATE_TEXT, "label")).to_equal(true)
```

</details>

#### emits an UpdateStyle op when computed_style changes

- draw ir batch
- draw ir box with style
- draw ir batch
- draw ir box with style
   - Expected: _op_kind_present(patch.operations, DRAW_IR_PATCH_OP_UPDATE_STYLE, "box") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline = draw_ir_composition("rev-1", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_box_with_style("box", 10, 10, 50, 20, 1u32, draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), [draw_ir_style_prop("fill", "blue")])
    ])
])
val current = draw_ir_composition("rev-2", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_box_with_style("box", 10, 10, 50, 20, 1u32, draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), [draw_ir_style_prop("fill", "red")])
    ])
])
val patch = draw_ir_patch_between(baseline, "rev-1", current, "rev-2")
expect(_op_kind_present(patch.operations, DRAW_IR_PATCH_OP_UPDATE_STYLE, "box")).to_equal(true)
```

</details>

#### emits a Reorder op only when content is identical but position moved

- draw ir batch
- draw ir rect
- draw ir rect
- draw ir batch
- draw ir rect
- draw ir rect
   - Expected: op.old_bounds.x equals `op.new_bounds.x`
   - Expected: reorder_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline = draw_ir_composition("rev-a", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("first", 0, 0, 10, 10, 1u32),
        draw_ir_rect("second", 20, 0, 10, 10, 2u32)
    ])
])
val current = draw_ir_composition("rev-b", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("second", 20, 0, 10, 10, 2u32),
        draw_ir_rect("first", 0, 0, 10, 10, 1u32)
    ])
])
val patch = draw_ir_patch_between(baseline, "rev-a", current, "rev-b")
var reorder_count = 0
for op in patch.operations:
    if op.kind == DRAW_IR_PATCH_OP_REORDER:
        reorder_count = reorder_count + 1
        expect(op.old_bounds.x).to_equal(op.new_bounds.x)
expect(reorder_count).to_equal(2)
```

</details>

#### does not emit Reorder when content also changed at a moved position

- draw ir batch
- draw ir rect
- draw ir rect
- draw ir batch
- draw ir rect
- draw ir rect
   - Expected: _op_kind_present(patch.operations, DRAW_IR_PATCH_OP_UPDATE_GEOMETRY, "first") is true
   - Expected: _op_kind_present(patch.operations, DRAW_IR_PATCH_OP_REORDER, "first") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline = draw_ir_composition("rev-a", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("first", 0, 0, 10, 10, 1u32),
        draw_ir_rect("second", 20, 0, 10, 10, 2u32)
    ])
])
val current = draw_ir_composition("rev-b", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("second", 20, 0, 10, 10, 2u32),
        draw_ir_rect("first", 99, 0, 10, 10, 1u32)
    ])
])
val patch = draw_ir_patch_between(baseline, "rev-a", current, "rev-b")
expect(_op_kind_present(patch.operations, DRAW_IR_PATCH_OP_UPDATE_GEOMETRY, "first")).to_equal(true)
expect(_op_kind_present(patch.operations, DRAW_IR_PATCH_OP_REORDER, "first")).to_equal(false)
```

</details>

#### covers damage_rects with the changed bounds

- draw ir batch
- draw ir rect
- draw ir batch
- draw ir rect
   - Expected: found_old is true
   - Expected: found_new is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline = draw_ir_composition("rev-1", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("box", 10, 10, 50, 20, 1u32)
    ])
])
val current = draw_ir_composition("rev-2", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("box", 30, 40, 55, 25, 1u32)
    ])
])
val patch = draw_ir_patch_between(baseline, "rev-1", current, "rev-2")
var found_old = false
var found_new = false
for rect in patch.damage_rects:
    if rect.x == 10 and rect.y == 10:
        found_old = true
    if rect.x == 30 and rect.y == 40:
        found_new = true
expect(found_old).to_equal(true)
expect(found_new).to_equal(true)
```

</details>

#### round-trips: apply(old, patch_between(old,new)) equals new command-by-command

- draw ir batch
- draw ir rect
- draw ir text
- draw ir rect
- draw ir batch
- draw ir rect
- draw ir text
- draw ir rect
   - Expected: applied.ok is true
   - Expected: draw_ir_patch_commands_equal(applied.composition, current) is true
   - Expected: applied.composition.composition_id equals `rev-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline = draw_ir_composition("rev-1", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("box", 10, 10, 50, 20, 1u32),
        draw_ir_text("label", 5, 5, "Old", 2u32),
        draw_ir_rect("gone", 90, 90, 10, 10, 3u32)
    ])
])
val current = draw_ir_composition("rev-2", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("box", 20, 30, 60, 25, 1u32),
        draw_ir_text("label", 5, 5, "New", 2u32),
        draw_ir_rect("fresh", 1, 1, 5, 5, 9u32)
    ])
])
val patch = draw_ir_patch_between(baseline, "rev-1", current, "rev-2")
val applied = draw_ir_patch_apply(baseline, patch)
expect(applied.ok).to_equal(true)
expect(draw_ir_patch_commands_equal(applied.composition, current)).to_equal(true)
expect(applied.composition.composition_id).to_equal("rev-2")
```

</details>

#### detects and round-trips a color-only in-place change with no geometry/style/text delta

- draw ir batch
- draw ir rect
- draw ir batch
- draw ir rect
   - Expected: patch.operations.len() > 0 is true
   - Expected: _op_kind_present(patch.operations, DRAW_IR_PATCH_OP_UPDATE_STYLE, "box") is true
   - Expected: _op_kind_present(patch.operations, DRAW_IR_PATCH_OP_REORDER, "box") is false
   - Expected: applied.ok is true
   - Expected: draw_ir_patch_commands_equal(applied.composition, current) is true
   - Expected: applied.composition.batches[0].commands[0].color equals `9u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline = draw_ir_composition("rev-1", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("box", 10, 10, 50, 20, 1u32)
    ])
])
val current = draw_ir_composition("rev-2", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("box", 10, 10, 50, 20, 9u32)
    ])
])
val patch = draw_ir_patch_between(baseline, "rev-1", current, "rev-2")
expect(patch.operations.len() > 0).to_equal(true)
expect(_op_kind_present(patch.operations, DRAW_IR_PATCH_OP_UPDATE_STYLE, "box")).to_equal(true)
expect(_op_kind_present(patch.operations, DRAW_IR_PATCH_OP_REORDER, "box")).to_equal(false)
val applied = draw_ir_patch_apply(baseline, patch)
expect(applied.ok).to_equal(true)
expect(draw_ir_patch_commands_equal(applied.composition, current)).to_equal(true)
expect(applied.composition.batches[0].commands[0].color).to_equal(9u32)
```

</details>

#### rejects apply when the composition revision does not match base_revision

- draw ir batch
- draw ir rect
- draw ir batch
- draw ir rect
- draw ir batch
- draw ir rect
   - Expected: rejected.ok is false
   - Expected: rejected.reason != "" is true
   - Expected: rejected.composition.composition_id equals `rev-STALE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline = draw_ir_composition("rev-1", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("box", 10, 10, 50, 20, 1u32)
    ])
])
val current = draw_ir_composition("rev-2", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("box", 30, 40, 55, 25, 1u32)
    ])
])
val patch = draw_ir_patch_between(baseline, "rev-1", current, "rev-2")
val stale = draw_ir_composition("rev-STALE", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_rect("box", 10, 10, 50, 20, 1u32)
    ])
])
val rejected = draw_ir_patch_apply(stale, patch)
expect(rejected.ok).to_equal(false)
expect(rejected.reason != "").to_equal(true)
expect(rejected.composition.composition_id).to_equal("rev-STALE")
```

</details>

#### round-trips a mixed ~30-command composition (insert/remove/geometry/text/style/reorder/unchanged)

- baseline cmds push
- current cmds push
- baseline cmds push
- current cmds push
- baseline cmds push
- current cmds push
- baseline cmds push
- current cmds push
- baseline cmds push
- baseline cmds push
- baseline cmds push
- baseline cmds push
- current cmds push
- current cmds push
- current cmds push
- current cmds push
- current cmds push
   - Expected: baseline_cmds.len() equals `26`
   - Expected: current_cmds.len() equals `27`
- draw ir batch
- draw ir batch
   - Expected: applied.ok is true
   - Expected: draw_ir_patch_commands_equal(applied.composition, current) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 65 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var baseline_cmds: [DrawIrCommand] = []
var current_cmds: [DrawIrCommand] = []

# c0..c4: geometry changes
var i = 0
while i < 5:
    val id = "geo{i}"
    baseline_cmds.push(draw_ir_rect(id, i * 10, i * 10, 20, 20, 1u32))
    current_cmds.push(draw_ir_rect(id, i * 10 + 100, i * 10 + 100, 20, 20, 1u32))
    i = i + 1

# c5..c9: text changes
i = 0
while i < 5:
    val id = "text{i}"
    baseline_cmds.push(draw_ir_text(id, i, i, "old{i}", 2u32))
    current_cmds.push(draw_ir_text(id, i, i, "new{i}", 2u32))
    i = i + 1

# c10..c14: style changes
i = 0
while i < 5:
    val id = "style{i}"
    baseline_cmds.push(draw_ir_box_with_style(id, i, i, 10, 10, 1u32, draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), [draw_ir_style_prop("fill", "blue")]))
    current_cmds.push(draw_ir_box_with_style(id, i, i, 10, 10, 1u32, draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), draw_ir_no_rect(), [draw_ir_style_prop("fill", "red")]))
    i = i + 1

# c15..c21: unchanged
i = 0
while i < 7:
    val id = "same{i}"
    val cmd = draw_ir_rect(id, i * 3, i * 3, 15, 15, 4u32)
    baseline_cmds.push(cmd)
    current_cmds.push(cmd)
    i = i + 1

# r0, r1: removed (baseline only)
baseline_cmds.push(draw_ir_rect("gone0", 200, 200, 5, 5, 5u32))
baseline_cmds.push(draw_ir_rect("gone1", 201, 201, 5, 5, 5u32))

# reordered pair: swap "reorder0" and "reorder1"
baseline_cmds.push(draw_ir_rect("reorder0", 300, 300, 5, 5, 6u32))
baseline_cmds.push(draw_ir_rect("reorder1", 310, 310, 5, 5, 7u32))
current_cmds.push(draw_ir_rect("reorder1", 310, 310, 5, 5, 7u32))
current_cmds.push(draw_ir_rect("reorder0", 300, 300, 5, 5, 6u32))

# inserted new items (current only)
current_cmds.push(draw_ir_rect("new0", 400, 400, 5, 5, 8u32))
current_cmds.push(draw_ir_rect("new1", 401, 401, 5, 5, 8u32))
current_cmds.push(draw_ir_rect("new2", 402, 402, 5, 5, 8u32))

expect(baseline_cmds.len()).to_equal(26)
expect(current_cmds.len()).to_equal(27)

val baseline = draw_ir_composition("mix-1", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), baseline_cmds)
])
val current = draw_ir_composition("mix-2", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), current_cmds)
])
val patch = draw_ir_patch_between(baseline, "mix-1", current, "mix-2")
val applied = draw_ir_patch_apply(baseline, patch)

expect(applied.ok).to_equal(true)
expect(draw_ir_patch_commands_equal(applied.composition, current)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
