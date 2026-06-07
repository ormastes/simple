# Draw Ir Diff Specification

> 1. draw ir batch

<!-- sdn-diagram:id=draw_ir_diff_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=draw_ir_diff_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

draw_ir_diff_spec -> std
draw_ir_diff_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=draw_ir_diff_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Draw Ir Diff Specification

## Scenarios

### Draw IR baseline diff

#### reports geometry style color border and text-bound deltas by stable id

1. draw ir batch

2. draw ir rect bounds

3. draw ir rect bounds

4. draw ir rect bounds

5. draw ir rect bounds

6. [draw ir style prop

7. draw ir text

8. draw ir batch

9. draw ir rect bounds

10. draw ir rect bounds

11. draw ir rect bounds

12. draw ir rect bounds

13. [draw ir style prop

14. draw ir text
   - Expected: report.node_count equals `2`
   - Expected: report.changed_count equals `2`
   - Expected: report.diffs[0].component_id equals `box`
   - Expected: report.diffs[0].dx equals `5`
   - Expected: report.diffs[0].dwidth equals `20`
   - Expected: report.diffs[0].color_changed is true
   - Expected: report.diffs[0].style_changed is true
   - Expected: report.diffs[0].border_changed is true
   - Expected: report.diffs[1].text_changed is true
   - Expected: report.diffs[1].text_bounds_changed is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline = draw_ir_composition("baseline", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_box_with_style(
            "box",
            10,
            20,
            100,
            40,
            1u32,
            draw_ir_rect_bounds(10, 20, 100, 40),
            draw_ir_rect_bounds(12, 22, 96, 36),
            draw_ir_rect_bounds(10, 20, 100, 40),
            draw_ir_rect_bounds(0, 0, 200, 100),
            [draw_ir_style_prop("fill", "blue")]
        ),
        draw_ir_text("label", 20, 30, "Old", 2u32)
    ])
])
val current = draw_ir_composition("current", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_box_with_style(
            "box",
            15,
            25,
            120,
            50,
            3u32,
            draw_ir_rect_bounds(15, 25, 120, 50),
            draw_ir_rect_bounds(17, 27, 116, 46),
            draw_ir_rect_bounds(15, 25, 120, 50),
            draw_ir_rect_bounds(0, 0, 200, 100),
            [draw_ir_style_prop("fill", "red")]
        ),
        draw_ir_text("label", 22, 33, "New", 2u32)
    ])
])

val report = draw_ir_diff_compositions(baseline, current)

expect(report.node_count).to_equal(2)
expect(report.changed_count).to_equal(2)
expect(report.diffs[0].component_id).to_equal("box")
expect(report.diffs[0].dx).to_equal(5)
expect(report.diffs[0].dwidth).to_equal(20)
expect(report.diffs[0].color_changed).to_equal(true)
expect(report.diffs[0].style_changed).to_equal(true)
expect(report.diffs[0].border_changed).to_equal(true)
expect(report.diffs[1].text_changed).to_equal(true)
expect(report.diffs[1].text_bounds_changed).to_equal(true)
```

</details>

#### reports added and removed nodes

1. draw ir batch

2. draw ir text

3. draw ir batch

4. draw ir text
   - Expected: report.added_count equals `1`
   - Expected: report.removed_count equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baseline = draw_ir_composition("baseline", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_text("removed", 5, 6, "Gone", 1u32)
    ])
])
val current = draw_ir_composition("current", "scene", DRAW_IR_BACKEND_CPU, [
    draw_ir_batch("batch", DRAW_IR_BACKEND_CPU, _embedding(), [
        draw_ir_text("added", 7, 8, "New", 1u32)
    ])
])

val report = draw_ir_diff_compositions(baseline, current)
val json = draw_ir_diff_report_to_json(report)

expect(report.added_count).to_equal(1)
expect(report.removed_count).to_equal(1)
expect(json).to_contain("\"state\":\"added\"")
expect(json).to_contain("\"state\":\"removed\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/draw_ir_diff_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Draw IR baseline diff

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
