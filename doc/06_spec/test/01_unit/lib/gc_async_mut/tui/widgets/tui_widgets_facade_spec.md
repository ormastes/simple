# Tui Widgets Facade Specification

> 1. var input = make input widget with value

<!-- sdn-diagram:id=tui_widgets_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tui_widgets_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tui_widgets_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tui_widgets_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tui Widgets Facade Specification

## Scenarios

### gc_async_mut tui widgets facade

#### re-exports text, box, list, and input widget behavior

1. var input = make input widget with value
2. input = input move home
3. input = input insert char
   - Expected: input.value equals `xab`
4. input = input delete back
   - Expected: input.value equals `ab`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = default_style()
val area = make_rect(0, 0, 10, 3)
val text_widget = make_text_widget_aligned("hi", style, ALIGN_CENTER)
expect(text_render(text_widget, area).len()).to_equal(3)
val box_widget = make_box_widget("T", style)
expect(box_inner_area(make_rect(0, 0, 10, 4)).width).to_equal(8)
val selected = list_select(make_list_widget(["a", "b"], style, style), 1)
expect(list_selected_item(selected)).to_equal("b")
var input = make_input_widget_with_value("> ", "ab", style)
input = input_move_home(input)
input = input_insert_char(input, "x")
expect(input.value).to_equal("xab")
input = input_delete_back(input)
expect(input.value).to_equal("ab")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/tui/widgets/tui_widgets_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut tui widgets facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
