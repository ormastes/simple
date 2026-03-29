# Dashboard HTML Rendering Specification

*Source: `test/app/web_dashboard/dashboard_render_spec.spl`*
*Last Updated: 2026-03-29*

**Feature IDs:** #DASH-001
**Category:** Tooling
**Difficulty:** 2/5
**Status:** Implemented
**Requirements:** N/A
**Plan:** N/A
**Design:** N/A
**Research:** N/A

---

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
use dashboard.render.colors.{status_css_class, html_badge}
use dashboard.render.progress.{render_progress_bar_html}
use dashboard.render.table.{render_html_table}

val badge = html_badge("complete", "complete")

val bar = render_progress_bar_html(75.0, "coverage")

val html = render_html_table(["Name", "Score"], [["Alice", "95"], ["Bob", "87"]])
```

## Status-to-CSS-Class Mapping

    Maps feature/test status strings to CSS badge classes used by
    both the web dashboard and generated HTML reports.

### Scenario: Standard status values

        Each status string maps to a specific CSS class for visual
        differentiation in the dashboard UI.

### Scenario: Percentage-based color thresholds

        Colors follow the standard traffic-light pattern:
        - >= 80%: green (healthy)
        - >= 60%: yellow (warning)
        - < 60%: red (critical)

### Scenario: Badge HTML generation

        Produces `<span class="badge {css_class}">{label}</span>` elements.

## Server-Side Progress Bar Rendering

    Progress bars are rendered server-side as inline-styled divs
    with percentage-based widths and threshold-based colors.
    Shared computation with CLI `render_progress_bar()`.

### Scenario: Progress bar with label and percentage

        Generates a two-part div: label row + bar with colored fill.

### Scenario: Fraction display with threshold coloring

        Shows "current/total" with color based on the ratio.

## HTML Table Generation

    Renders data as `<table class="data-table">` elements with
    headers and rows. Supports row limiting for large datasets.
    Shared structure with CLI `TableBuilder.render()`.

### Scenario: Full table rendering

        Produces a complete HTML table with `<th>` headers and `<td>` cells.

### Scenario: Row-limited table for large datasets

        Truncates output to max_rows, preventing oversized HTML
        in the dashboard status view.

## Test Summary

| Metric | Count |
|--------|-------|
| Scenarios | 27 |
| Slow Scenarios | 0 |
| Skipped Scenarios | 0 |

## Scenarios

- maps complete to badge-green
- maps in_progress to badge-yellow
- maps planned to badge-blue
- maps failed to badge-red
- maps blocked to badge-red
- maps passed to badge-green
- returns empty string for unknown status
- returns green for high percentage
- returns yellow for medium percentage
- returns red for low percentage
- returns green at exactly 80%
- returns yellow at exactly 60%
- wraps label in badge span with correct class
- uses status-based class for different statuses
- renders bar with correct percentage
- caps width at 100% for over-100 values
- uses green color for high percentage
- uses yellow color for medium percentage
- uses red color for low percentage
- handles zero percentage
- renders fraction with green for high ratio
- renders fraction with red for low ratio
- handles zero total without crashing
- renders table with headers and rows
- renders empty table with headers only
- limits rows to specified maximum
- renders all rows when under limit
