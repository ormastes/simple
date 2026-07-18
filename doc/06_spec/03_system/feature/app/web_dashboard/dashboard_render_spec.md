# Dashboard HTML Rendering Specification

> Tests the merged dashboard rendering layer that is shared between the CLI (ANSI terminal) and web (HTML) output modes. The rendering components live in `dashboard.render/` and `dashboard.views/status.spl`.

<!-- sdn-diagram:id=dashboard_render_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dashboard_render_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dashboard_render_spec -> app
dashboard_render_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dashboard_render_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dashboard HTML Rendering Specification

Tests the merged dashboard rendering layer that is shared between the CLI (ANSI terminal) and web (HTML) output modes. The rendering components live in `dashboard.render/` and `dashboard.views/status.spl`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DASH-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/feature/app/web_dashboard/dashboard_render_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the merged dashboard rendering layer that is shared between
the CLI (ANSI terminal) and web (HTML) output modes. The rendering
components live in `dashboard.render/` and `dashboard.views/status.spl`.

This spec validates the HTML output functions added to the existing
ANSI rendering layer:
- `colors.spl`: CSS class mapping, threshold colors, badge generation
- `progress.spl`: HTML progress bars and fraction displays
- `table.spl`: HTML table rendering with row limits

## Key Concepts

| Concept | Description |
|---------|-------------|
| status_css_class | Maps status strings to CSS badge class names |
| threshold_css_color | Returns CSS color variable based on percentage thresholds |
| html_badge | Wraps a label in a styled `<span>` badge |
| render_progress_bar_html | Server-side rendered progress bar div |
| render_html_table | Generates `<table>` from headers and row data |
| Shared rendering | Same computation logic, dual output (ANSI + HTML) |

## Behavior

- CSS classes follow the pattern `badge-{color}` (green, yellow, red, blue)
- Threshold colors use CSS custom properties with fallback hex values
- Progress bar width is capped at 100% even for values > 100
- Table rendering supports row limits for large datasets
- All functions produce valid HTML fragments (no full documents)

## Related Specifications

- Tmux API spec — tests the tmux integration used by the terminal panel
- Web dashboard server — uses these renderers for server-side HTML

## Examples

```simple
use app.dashboard.render.colors.{status_css_class, html_badge}
use app.dashboard.render.progress.{render_progress_bar_html}
use app.dashboard.render.table.{render_html_table}

# Status badge
val badge = html_badge("complete", "complete")
# => <span class="badge badge-green">complete</span>

# Progress bar
val bar = render_progress_bar_html(75.0, "coverage")
# => <div>...<div style="width:75%;background:var(--yellow,...)">...</div></div>

# HTML table
val html = render_html_table(["Name", "Score"], [["Alice", "95"], ["Bob", "87"]])
# => <table class="data-table">...</table>
```

## Scenarios

### Dashboard CSS Color Mapping

#### status_css_class

#### maps complete to badge-green

1. expect status css class


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect status_css_class("complete") to_equal "badge-green"
```

</details>

#### maps in_progress to badge-yellow

1. expect status css class


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect status_css_class("in_progress") to_equal "badge-yellow"
```

</details>

#### maps planned to badge-blue

1. expect status css class


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect status_css_class("planned") to_equal "badge-blue"
```

</details>

#### maps failed to badge-red

1. expect status css class


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect status_css_class("failed") to_equal "badge-red"
```

</details>

#### maps blocked to badge-red

1. expect status css class


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect status_css_class("blocked") to_equal "badge-red"
```

</details>

#### maps passed to badge-green

1. expect status css class


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect status_css_class("passed") to_equal "badge-green"
```

</details>

#### returns empty string for unknown status

1. expect status css class


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect status_css_class("unknown") to_equal ""
```

</details>

#### threshold_css_color

#### returns green for high percentage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = threshold_css_color(85.0)
expect color to_contain "3fb950"
```

</details>

#### returns yellow for medium percentage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = threshold_css_color(70.0)
expect color to_contain "d29922"
```

</details>

#### returns red for low percentage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = threshold_css_color(40.0)
expect color to_contain "f85149"
```

</details>

#### returns green at exactly 80%

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = threshold_css_color(80.0)
expect color to_contain "3fb950"
```

</details>

#### returns yellow at exactly 60%

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val color = threshold_css_color(60.0)
expect color to_contain "d29922"
```

</details>

#### html_badge

#### wraps label in badge span with correct class

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val badge = html_badge("complete", "complete")
expect badge to_contain "badge-green"
expect badge to_contain "complete"
expect(badge).to_start_with("<span")
```

</details>

#### uses status-based class for different statuses

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val badge = html_badge("P0", "failed")
expect badge to_contain "badge-red"
expect badge to_contain "P0"
```

</details>

### Dashboard HTML Progress Bars

#### render_progress_bar_html

#### renders bar with correct percentage

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = render_progress_bar_html(75.0, "coverage")
expect bar to_contain "75"
expect bar to_contain "coverage"
expect bar to_contain "width:75%"
```

</details>

#### caps width at 100% for over-100 values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = render_progress_bar_html(150.0, "over")
expect bar to_contain "width:100%"
```

</details>

#### uses green color for high percentage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = render_progress_bar_html(90.0, "test")
expect bar to_contain "3fb950"
```

</details>

#### uses yellow color for medium percentage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = render_progress_bar_html(65.0, "test")
expect bar to_contain "d29922"
```

</details>

#### uses red color for low percentage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = render_progress_bar_html(30.0, "test")
expect bar to_contain "f85149"
```

</details>

#### handles zero percentage

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bar = render_progress_bar_html(0.0, "empty")
expect bar to_contain "width:0%"
expect bar to_contain "empty"
```

</details>

#### render_fraction_html

#### renders fraction with green for high ratio

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frac = render_fraction_html(8, 10)
expect frac to_contain "8/10"
expect frac to_contain "3fb950"
```

</details>

#### renders fraction with red for low ratio

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frac = render_fraction_html(1, 10)
expect frac to_contain "1/10"
expect frac to_contain "f85149"
```

</details>

#### handles zero total without crashing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frac = render_fraction_html(0, 0)
expect frac to_contain "0/0"
```

</details>

### Dashboard HTML Table Rendering

#### render_html_table

#### renders table with headers and rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = ["Name", "Value"]
val rows = [["foo", "1"], ["bar", "2"]]
val html = render_html_table(headers, rows)
expect html to_contain "<table"
expect html to_contain "data-table"
expect html to_contain "<th>Name</th>"
expect html to_contain "<th>Value</th>"
expect html to_contain "<td>foo</td>"
expect html to_contain "<td>2</td>"
```

</details>

#### renders empty table with headers only

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = ["A", "B"]
val rows: [[text]] = []
val html = render_html_table(headers, rows)
expect html to_contain "<th>A</th>"
expect html to_contain "</table>"
```

</details>

#### render_html_table_limited

#### limits rows to specified maximum

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = ["X"]
val rows = [["a"], ["b"], ["c"], ["d"], ["e"]]
val html = render_html_table_limited(headers, rows, 3)
expect html to_contain "<td>a</td>"
expect html to_contain "<td>c</td>"
val has_d = html.contains("<td>d</td>")
expect has_d to_equal false
```

</details>

#### renders all rows when under limit

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val headers = ["X"]
val rows = [["a"], ["b"]]
val html = render_html_table_limited(headers, rows, 10)
expect html to_contain "<td>a</td>"
expect html to_contain "<td>b</td>"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
