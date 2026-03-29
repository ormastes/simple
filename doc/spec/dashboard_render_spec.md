*Source: `test/app/web_dashboard/dashboard_render_spec.spl`*
*Last Updated: 2026-03-29*

---

# Dashboard HTML Rendering Specification

**Feature IDs:** #DASH-001
**Category:** Tooling
**Difficulty:** 2/5
**Status:** Implemented
**Requirements:** N/A
**Plan:** N/A
**Design:** N/A
**Research:** N/A

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
