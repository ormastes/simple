# Md Draw Ir Specification

> <details>

<!-- sdn-diagram:id=md_draw_ir_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=md_draw_ir_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

md_draw_ir_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=md_draw_ir_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Md Draw Ir Specification

## Scenarios

### md_draw_ir line projection

#### emits one TEXT draw-IR command per rendered line

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ["alpha", "beta", "gamma"]
val cmds = md_draw_ir_commands_from_lines(lines, "doc")
expect(cmds.len()).to_equal(3)
expect(cmds[0].kind).to_equal(DRAW_IR_COMMAND_TEXT)
expect(cmds[1].kind).to_equal(DRAW_IR_COMMAND_TEXT)
expect(cmds[2].kind).to_equal(DRAW_IR_COMMAND_TEXT)
```

</details>

#### carries the line text verbatim as the TEXT payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ["first line", "second line"]
val cmds = md_draw_ir_commands_from_lines(lines, "doc")
expect(cmds[0].text_value).to_equal("first line")
expect(cmds[1].text_value).to_equal("second line")
```

</details>

#### stacks lines vertically by y position

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ["a", "b", "c"]
val cmds = md_draw_ir_commands_from_lines(lines, "doc")
expect(cmds[0].y).to_equal(0)
expect(cmds[1].y).to_equal(1)
expect(cmds[2].y).to_equal(2)
```

</details>

#### addresses each line with a component_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmds = md_draw_ir_commands_from_lines(["only"], "doc")
expect(cmds[0].component_id).to_equal("doc:line:0")
```

</details>

### md_draw_ir BlockModel composition

#### wraps a BlockModel render into a single-batch composition

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("# Title\n\nbody text")
val comp = md_draw_ir_composition(model, "ed", DRAW_IR_BACKEND_GPU)
expect(comp.batches.len()).to_equal(1)
expect(comp.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
```

</details>

#### produces a TEXT command for every rendered TUI line

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("# Title\n\nbody text")
val expected_lines = md_render_blocks(model)
val comp = md_draw_ir_composition(model, "ed", DRAW_IR_BACKEND_GPU)
val cmds = comp.batches[0].commands
expect(cmds.len()).to_equal(expected_lines.len())
var i = 0
var all_text = true
while i < cmds.len():
    if cmds[i].kind != DRAW_IR_COMMAND_TEXT:
        all_text = false
    i = i + 1
expect(all_text).to_equal(true)
```

</details>

#### flows shared-cascade heading style into the projected draw-IR text

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# heading_1 -> font-weight bold -> SGR "1" (from office_style_resolver),
# layered with the TUI color "33". The rendered heading line therefore
# begins with ESC[33;1m and that exact styled text is carried in the IR.
val model = BlockModel.from_markdown("# Hello")
val comp = md_draw_ir_composition(model, "ed", DRAW_IR_BACKEND_AUTO)
val cmds = comp.batches[0].commands
expect(cmds.len()).to_be_greater_than(0)
val first = cmds[0].text_value
expect(first.contains("\x1b[33;1m")).to_equal(true)
expect(first.contains("Hello")).to_equal(true)
```

</details>

#### auto composition selects the AUTO backend lane like the GUI

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val model = BlockModel.from_markdown("# Title")
val comp = md_draw_ir_composition_auto(model, "ed")
expect(comp.backend_target).to_equal(DRAW_IR_BACKEND_AUTO)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/render/md_draw_ir_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- md_draw_ir line projection
- md_draw_ir BlockModel composition

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
