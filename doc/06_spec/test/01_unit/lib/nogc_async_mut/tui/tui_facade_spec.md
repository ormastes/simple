# Tui Facade Specification

> <details>

<!-- sdn-diagram:id=tui_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tui_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tui_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tui_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tui Facade Specification

## Scenarios

### nogc_async_mut tui facades

#### re-exports pure TUI style, widget, and layout helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val style = make_style(COLOR_RED, COLOR_NONE, true, false, false, false)
expect(render_line(make_styled_line("err", style)).contains("err")).to_equal(true)
expect(render_line(make_plain_line("plain"))).to_equal("plain")
val rgb_style = make_style_rgb(RgbColor(r: 1, g: 2, b: 3), RgbColor(r: 4, g: 5, b: 6), false, false, false, false)
expect(rgb_style.fg_rgb.g).to_equal(2)
expect(fg_style(COLOR_RED).fg).to_equal(COLOR_RED)
expect(bold_style().bold).to_equal(true)

val area = make_rect(0, 0, 80, 24)
val inner = rect_inner(area, 1, 2, 3, 4)
expect(inner.x).to_equal(4)
expect(inner.width).to_equal(74)
expect(rect_area(area)).to_equal(1920)
expect(rect_right(area)).to_equal(80)
expect(rect_bottom(area)).to_equal(24)
expect(rect_contains(area, 10, 10)).to_equal(true)
expect(pad_or_truncate("abc", 5)).to_equal("abc  ")
expect(pad_or_truncate("abcdef", 3)).to_equal("abc")

val buf = buffer_set_line(make_render_buffer(5, 2), 1, make_plain_line("row"))
expect(buf.lines[1].segments[0].content).to_equal("row")

expect(split_vertical(area, [1, 1]).len()).to_equal(2)
expect(split_horizontal(area, [1, 1])[1].x).to_equal(40)
expect(split_vertical_fixed(area, [5, -1])[1].height).to_equal(19)
expect(split_horizontal_fixed(area, [10, -1])[1].width).to_equal(70)
expect(apply_margin(area, make_margin(1, 2, 3, 4)).x).to_equal(4)
expect(apply_margin(area, make_uniform_margin(2)).width).to_equal(76)
expect(center_rect(area, 20, 10).x).to_equal(30)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/tui/tui_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut tui facades

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
