# BrowserSession HTML table text projection

> Projects supported caption, row, and cell boundaries to visible text. This is

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# BrowserSession HTML table text projection

Projects supported caption, row, and cell boundaries to visible text. This is

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/browser_session_html_table_tags_spec.spl` |
| Updated | 2026-07-29 |
| Generator | `simple spipe-docgen` (Simple) |

Projects supported caption, row, and cell boundaries to visible text. This is
not table layout, Draw IR, or pixel evidence.

## Scenarios

### BrowserSession HTML table tag text semantics

#### should preserve caption row and cell boundaries for table text

- Project supported HTML semantics to visible text
   - Expected: html_to_text(html) equals `Scores\nName\tScore\nAda\t10\nTotal\t10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project supported HTML semantics to visible text")
val html = "<table><caption>Scores</caption><colgroup><col></colgroup><thead><tr><th>Name</th><th>Score</th></tr></thead><tbody><tr><td>Ada</td><td>10</td></tr></tbody><tfoot><tr><td>Total</td><td>10</td></tr></tfoot></table>"
expect(html_to_text(html)).to_equal("Scores\nName\tScore\nAda\t10\nTotal\t10")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
