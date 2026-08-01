# Report Specification

> <details>

<!-- sdn-diagram:id=report_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=report_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

report_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=report_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Report Specification

## Scenarios

### Chrome vs Simple — Report Shape

#### loads all four fixture rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
expect(row_count(rows)).to_equal(4)
```

</details>

#### all rows have required fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
expect(all_rows_have_fields(rows)).to_equal(true)
```

</details>

#### all status values are valid

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
expect(all_statuses_valid(rows)).to_equal(true)
```

</details>

#### simple_vs_chrome_ratio is non-negative for static_page

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
val row = find_row(rows, "static_page")
expect(row.simple_vs_chrome_ratio >= 0.0).to_equal(true)
```

</details>

#### pixel_hash_simple is non-empty for static_page

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
val row = find_row(rows, "static_page")
expect(row.pixel_hash_simple.len() > 0).to_equal(true)
```

</details>

#### pixel_hash_chrome field is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
val row = find_row(rows, "static_page")
expect(row.pixel_hash_chrome.len() >= 0).to_equal(true)
```

</details>

#### pixel_match_pct is non-negative for static_page

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
val row = find_row(rows, "static_page")
expect(row.pixel_match_pct >= 0.0).to_equal(true)
```

</details>

#### all four fixture names appear in loaded rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
val has_static  = find_row(rows, "static_page").fixture == "static_page"
val has_scroll  = find_row(rows, "scroll_heavy").fixture == "scroll_heavy"
val has_layout  = find_row(rows, "layout_stress").fixture == "layout_stress"
val has_paint   = find_row(rows, "paint_heavy").fixture == "paint_heavy"
expect(has_static and has_scroll and has_layout and has_paint).to_equal(true)
```

</details>

### Chrome vs Simple — Threshold Math

#### ratio = simple_frame_ms / chrome_frame_ms for static_page

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
expect(ratio_correct_for(find_row(rows, "static_page"))).to_equal(true)
```

</details>

#### ratio = simple_frame_ms / chrome_frame_ms for scroll_heavy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
expect(ratio_correct_for(find_row(rows, "scroll_heavy"))).to_equal(true)
```

</details>

<details>
<summary>Advanced: ratio = simple_frame_ms / chrome_frame_ms for layout_stress</summary>

#### ratio = simple_frame_ms / chrome_frame_ms for layout_stress

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
expect(ratio_correct_for(find_row(rows, "layout_stress"))).to_equal(true)
```

</details>


</details>

#### ratio = simple_frame_ms / chrome_frame_ms for paint_heavy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
expect(ratio_correct_for(find_row(rows, "paint_heavy"))).to_equal(true)
```

</details>

#### stage breakdown sums within 20pct of total for static_page

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
expect(stage_sum_near_total(find_row(rows, "static_page"))).to_equal(true)
```

</details>

#### stage breakdown sums within 20pct of total for scroll_heavy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
expect(stage_sum_near_total(find_row(rows, "scroll_heavy"))).to_equal(true)
```

</details>

<details>
<summary>Advanced: stage breakdown sums within 20pct of total for layout_stress</summary>

#### stage breakdown sums within 20pct of total for layout_stress

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
expect(stage_sum_near_total(find_row(rows, "layout_stress"))).to_equal(true)
```

</details>


</details>

#### stage breakdown sums within 20pct of total for paint_heavy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
expect(stage_sum_near_total(find_row(rows, "paint_heavy"))).to_equal(true)
```

</details>

### Chrome vs Simple — NFR 2B Compliance

#### static_page is PENDING or within 16.7ms p95

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
expect(nfr_2b_ok(find_row(rows, "static_page"))).to_equal(true)
```

</details>

#### scroll_heavy is PENDING or within 16.7ms p95

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
expect(nfr_2b_ok(find_row(rows, "scroll_heavy"))).to_equal(true)
```

</details>

<details>
<summary>Advanced: layout_stress is PENDING or within 16.7ms p95</summary>

#### layout_stress is PENDING or within 16.7ms p95

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
expect(nfr_2b_ok(find_row(rows, "layout_stress"))).to_equal(true)
```

</details>


</details>

#### paint_heavy is PENDING or within 16.7ms p95

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
expect(nfr_2b_ok(find_row(rows, "paint_heavy"))).to_equal(true)
```

</details>

#### synthetic rows yield PENDING status — no false greens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
expect(all_synthetic_are_pending(rows)).to_equal(true)
```

</details>

#### source field is valid for static_page

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
expect(source_valid(find_row(rows, "static_page"))).to_equal(true)
```

</details>

### Chrome vs Simple — classify_status

#### returns FAIL when measured frame_ms exceeds 16.7

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = classify_status("measured", 20.0, 1.2, 99.5)
expect(status).to_equal("FAIL")
```

</details>

#### returns FAIL when measured ratio exceeds 2.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = classify_status("measured", 10.0, 2.5, 99.5)
expect(status).to_equal("FAIL")
```

</details>

#### returns FAIL when measured pixel_match below 95

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = classify_status("measured", 10.0, 1.2, 90.0)
expect(status).to_equal("FAIL")
```

</details>

#### returns PASS for healthy measured data

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = classify_status("measured", 10.0, 1.2, 99.5)
expect(status).to_equal("PASS")
```

</details>

#### returns WARN when ratio between 1.5 and 2.0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = classify_status("measured", 10.0, 1.8, 99.5)
expect(status).to_equal("WARN")
```

</details>

#### returns PENDING for synthetic regardless of timings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = classify_status("synthetic", 5.0, 0.8, 100.0)
expect(status).to_equal("PENDING")
```

</details>

### Chrome vs Simple — Report Output

#### prints full comparison report without error

1. print report
   - Expected: row_count(rows) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rows = load_all_rows()
print_report(rows)
expect(row_count(rows)).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/web_render_chrome/report_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Chrome vs Simple — Report Shape
- Chrome vs Simple — Threshold Math
- Chrome vs Simple — NFR 2B Compliance
- Chrome vs Simple — classify_status
- Chrome vs Simple — Report Output

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
