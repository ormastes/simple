# Md Renderer Table Align Specification

> <details>

<!-- sdn-diagram:id=md_renderer_table_align_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=md_renderer_table_align_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

md_renderer_table_align_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=md_renderer_table_align_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Renderer Table Align Specification

## Scenarios

### table column alignment

#### pads cells to uniform column width

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("| Name | Age |\n| --- | --- |\n| Alexandra | 7 |")
val lines = md_render_block(model.block_at(0))
expect(lines.len()).to_equal(3)
expect(lines[0]).to_equal("| Name      | Age |")
expect(lines[2]).to_equal("| Alexandra | 7   |")
```

</details>

#### right-aligns columns marked --:

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("| Score |\n| ---: |\n| 42 |")
val lines = md_render_block(model.block_at(0))
expect(lines[0]).to_equal("| Score |")
expect(lines[2]).to_equal("|    42 |")
expect(lines[1].index_of("----:") >= 0).to_equal(true)
```

</details>

#### centers columns marked :-:

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("| City |\n| :-: |\n| NY |")
val lines = md_render_block(model.block_at(0))
expect(lines[2]).to_equal("|  NY  |")
expect(lines[1].index_of(":--:") >= 0).to_equal(true)
```

</details>

#### rows with missing cells are padded to the full grid

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("| A | B | C |\n| --- | --- |\n| 1 | 2 | 3 | 4 |")
val lines = md_render_block(model.block_at(0))
expect(lines.len()).to_equal(3)
expect(lines[0].len()).to_equal(lines[2].len())
```

</details>

#### table without separator row still renders a padded grid

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("| Name | Age |\n| Alexandra | 7 |")
val lines = md_render_block(model.block_at(0))
expect(lines.len()).to_equal(2)
expect(lines[0]).to_equal("| Name      | Age |")
expect(lines[1]).to_equal("| Alexandra | 7   |")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/render/md_renderer_table_align_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- table column alignment

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
