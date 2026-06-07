# Block Model Specification

> <details>

<!-- sdn-diagram:id=block_model_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=block_model_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

block_model_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=block_model_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Block Model Specification

## Scenarios

### markdown block model

#### parses source ranges and common markdown block kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "# Title\n\nParagraph text\n\n- [ ] Task\n\n| A | B |\n| --- | --- |\n| 1 | 2 |\n\n> [!NOTE]- Folded\n> Body\n\n![Diagram](assets/a.png)\n\n```sdn-graph\nA -> B\n```"
val model = BlockModel.from_markdown(source)

expect(model.block_count()).to_equal(6)
expect(model.block_at(0).kind).to_equal("heading")
expect(model.block_at(0).from_line).to_equal(0)
expect(model.block_at(1).kind).to_equal("paragraph")
expect(model.block_at(2).kind).to_equal("list")
expect(model.block_at(3).kind).to_equal("table")
expect(model.block_at(3).from_line).to_equal(6)
expect(model.block_at(3).to_line).to_equal(8)
expect(model.block_at(4).kind).to_equal("callout")
expect(model.block_at(5).kind).to_equal("embed")
```

</details>

#### tracks active block and cursor mapping

1. var model = BlockModel from markdown
   - Expected: model.block_for_line(2) equals `1`
   - Expected: bm_cursor_block_index(model, 5) equals `2`
   - Expected: bm_cursor_block_changed(model, 2) is true
2. model activate block
   - Expected: model.active_block equals `1`
   - Expected: model.is_active(1) is true
   - Expected: bm_cursor_block_changed(model, 2) is false
   - Expected: bm_active_block_range(model) equals `2`
   - Expected: render_block_line_span(model.block_at(1)) equals `2`
3. model deactivate block
   - Expected: model.active_block equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var model = BlockModel.from_markdown("# Title\n\nFirst paragraph\nsecond line\n\n## Next")

expect(model.block_for_line(2)).to_equal(1)
expect(bm_cursor_block_index(model, 5)).to_equal(2)
expect(bm_cursor_block_changed(model, 2)).to_equal(true)

model.activate_block(1)
expect(model.active_block).to_equal(1)
expect(model.is_active(1)).to_equal(true)
expect(bm_cursor_block_changed(model, 2)).to_equal(false)
expect(bm_active_block_range(model)).to_equal(2)
expect(render_block_line_span(model.block_at(1))).to_equal(2)

model.deactivate_block()
expect(model.active_block).to_equal(-1)
```

</details>

#### rebuilds blocks and resets active state

1. var model = BlockModel from markdown
2. model activate block
3. model rebuild
   - Expected: model.block_count() equals `1`
   - Expected: model.block_at(0).kind equals `paragraph`
   - Expected: model.active_block equals `-1`
   - Expected: model.next_id equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var model = BlockModel.from_markdown("# Old")
model.activate_block(0)
model.rebuild("plain\ntext")

expect(model.block_count()).to_equal(1)
expect(model.block_at(0).kind).to_equal("paragraph")
expect(model.active_block).to_equal(-1)
expect(model.next_id).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/block_model_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- markdown block model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
