# Report Specification

> Tests covering Chrome vs Simple — Report Shape, Chrome vs Simple — Threshold Math, Chrome vs Simple — NFR 2B Compliance, Chrome vs Simple — classify_status, Chrome vs Simple — Report Output.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Report Specification

## Scenarios

### Chrome vs Simple — Report Shape

#### loads all four fixture rows

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads all four fixture rows
   - Expected: row_count(rows) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("loads all four fixture rows")
val rows = load_all_rows()
expect(row_count(rows)).to_equal(4)
```

</details>

#### all rows have required fields

- all rows have required fields
   - Expected: all_rows_have_fields(rows) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("all rows have required fields")
val rows = load_all_rows()
expect(all_rows_have_fields(rows)).to_equal(true)
```

</details>

#### all status values are valid

- all status values are valid
   - Expected: all_statuses_valid(rows) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("all status values are valid")
val rows = load_all_rows()
expect(all_statuses_valid(rows)).to_equal(true)
```

</details>

#### simple_vs_chrome_ratio is non-negative for static_page

- simple_vs_chrome_ratio is non-negative for static_page
   - Expected: row.simple_vs_chrome_ratio >= 0.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("simple_vs_chrome_ratio is non-negative for static_page")
val rows = load_all_rows()
val row = find_row(rows, "static_page")
expect(row.simple_vs_chrome_ratio >= 0.0).to_equal(true)
```

</details>

#### pixel_hash_simple is non-empty for static_page

- pixel_hash_simple is non-empty for static_page
   - Expected: row.pixel_hash_simple.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("pixel_hash_simple is non-empty for static_page")
val rows = load_all_rows()
val row = find_row(rows, "static_page")
expect(row.pixel_hash_simple.len() > 0).to_equal(true)
```

</details>

#### pixel_hash_chrome field is present

- pixel_hash_chrome field is present
   - Expected: row.pixel_hash_chrome.len() >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("pixel_hash_chrome field is present")
val rows = load_all_rows()
val row = find_row(rows, "static_page")
expect(row.pixel_hash_chrome.len() >= 0).to_equal(true)
```

</details>

#### pixel_match_pct is non-negative for static_page

- pixel_match_pct is non-negative for static_page
   - Expected: row.pixel_match_pct >= 0.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("pixel_match_pct is non-negative for static_page")
val rows = load_all_rows()
val row = find_row(rows, "static_page")
expect(row.pixel_match_pct >= 0.0).to_equal(true)
```

</details>

#### all four fixture names appear in loaded rows

- all four fixture names appear in loaded rows
   - Expected: has_static and has_scroll and has_layout and has_paint is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("all four fixture names appear in loaded rows")
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

- ratio = simple_frame_ms / chrome_frame_ms for static_page
   - Expected: ratio_correct_for(find_row(rows, "static_page")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("ratio = simple_frame_ms / chrome_frame_ms for static_page")
val rows = load_all_rows()
expect(ratio_correct_for(find_row(rows, "static_page"))).to_equal(true)
```

</details>

#### ratio = simple_frame_ms / chrome_frame_ms for scroll_heavy

- ratio = simple_frame_ms / chrome_frame_ms for scroll_heavy
   - Expected: ratio_correct_for(find_row(rows, "scroll_heavy")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("ratio = simple_frame_ms / chrome_frame_ms for scroll_heavy")
val rows = load_all_rows()
expect(ratio_correct_for(find_row(rows, "scroll_heavy"))).to_equal(true)
```

</details>

<details>
<summary>Advanced: ratio = simple_frame_ms / chrome_frame_ms for layout_stress</summary>

#### ratio = simple_frame_ms / chrome_frame_ms for layout_stress

- ratio = simple_frame_ms / chrome_frame_ms for layout_stress
   - Expected: ratio_correct_for(find_row(rows, "layout_stress")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("ratio = simple_frame_ms / chrome_frame_ms for layout_stress")
val rows = load_all_rows()
expect(ratio_correct_for(find_row(rows, "layout_stress"))).to_equal(true)
```

</details>


</details>

#### ratio = simple_frame_ms / chrome_frame_ms for paint_heavy

- ratio = simple_frame_ms / chrome_frame_ms for paint_heavy
   - Expected: ratio_correct_for(find_row(rows, "paint_heavy")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("ratio = simple_frame_ms / chrome_frame_ms for paint_heavy")
val rows = load_all_rows()
expect(ratio_correct_for(find_row(rows, "paint_heavy"))).to_equal(true)
```

</details>

#### stage breakdown sums within 20pct of total for static_page

- stage breakdown sums within 20pct of total for static_page
   - Expected: stage_sum_near_total(find_row(rows, "static_page")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("stage breakdown sums within 20pct of total for static_page")
val rows = load_all_rows()
expect(stage_sum_near_total(find_row(rows, "static_page"))).to_equal(true)
```

</details>

#### stage breakdown sums within 20pct of total for scroll_heavy

- stage breakdown sums within 20pct of total for scroll_heavy
   - Expected: stage_sum_near_total(find_row(rows, "scroll_heavy")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("stage breakdown sums within 20pct of total for scroll_heavy")
val rows = load_all_rows()
expect(stage_sum_near_total(find_row(rows, "scroll_heavy"))).to_equal(true)
```

</details>

<details>
<summary>Advanced: stage breakdown sums within 20pct of total for layout_stress</summary>

#### stage breakdown sums within 20pct of total for layout_stress

- stage breakdown sums within 20pct of total for layout_stress
   - Expected: stage_sum_near_total(find_row(rows, "layout_stress")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("stage breakdown sums within 20pct of total for layout_stress")
val rows = load_all_rows()
expect(stage_sum_near_total(find_row(rows, "layout_stress"))).to_equal(true)
```

</details>


</details>

#### stage breakdown sums within 20pct of total for paint_heavy

- stage breakdown sums within 20pct of total for paint_heavy
   - Expected: stage_sum_near_total(find_row(rows, "paint_heavy")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("stage breakdown sums within 20pct of total for paint_heavy")
val rows = load_all_rows()
expect(stage_sum_near_total(find_row(rows, "paint_heavy"))).to_equal(true)
```

</details>

### Chrome vs Simple — NFR 2B Compliance

#### static_page is PENDING or within 16.7ms p95

- static_page is PENDING or within 16.7ms p95
   - Expected: nfr_2b_ok(find_row(rows, "static_page")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("static_page is PENDING or within 16.7ms p95")
val rows = load_all_rows()
expect(nfr_2b_ok(find_row(rows, "static_page"))).to_equal(true)
```

</details>

#### scroll_heavy is PENDING or within 16.7ms p95

- scroll_heavy is PENDING or within 16.7ms p95
   - Expected: nfr_2b_ok(find_row(rows, "scroll_heavy")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("scroll_heavy is PENDING or within 16.7ms p95")
val rows = load_all_rows()
expect(nfr_2b_ok(find_row(rows, "scroll_heavy"))).to_equal(true)
```

</details>

<details>
<summary>Advanced: layout_stress is PENDING or within 16.7ms p95</summary>

#### layout_stress is PENDING or within 16.7ms p95

- layout_stress is PENDING or within 16.7ms p95
   - Expected: nfr_2b_ok(find_row(rows, "layout_stress")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("layout_stress is PENDING or within 16.7ms p95")
val rows = load_all_rows()
expect(nfr_2b_ok(find_row(rows, "layout_stress"))).to_equal(true)
```

</details>


</details>

#### paint_heavy is PENDING or within 16.7ms p95

- paint_heavy is PENDING or within 16.7ms p95
   - Expected: nfr_2b_ok(find_row(rows, "paint_heavy")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("paint_heavy is PENDING or within 16.7ms p95")
val rows = load_all_rows()
expect(nfr_2b_ok(find_row(rows, "paint_heavy"))).to_equal(true)
```

</details>

#### synthetic rows yield PENDING status — no false greens

- synthetic rows yield PENDING status — no false greens
   - Expected: all_synthetic_are_pending(rows) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("synthetic rows yield PENDING status — no false greens")
val rows = load_all_rows()
expect(all_synthetic_are_pending(rows)).to_equal(true)
```

</details>

#### source field is valid for static_page

- source field is valid for static_page
   - Expected: source_valid(find_row(rows, "static_page")) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("source field is valid for static_page")
val rows = load_all_rows()
expect(source_valid(find_row(rows, "static_page"))).to_equal(true)
```

</details>

### Chrome vs Simple — classify_status

#### returns FAIL when measured frame_ms exceeds 16.7

- returns FAIL when measured frame_ms exceeds 16.7
   - Expected: status equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("returns FAIL when measured frame_ms exceeds 16.7")
val status = classify_status("measured", 20.0, 1.2, 99.5)
expect(status).to_equal("FAIL")
```

</details>

#### returns FAIL when measured ratio exceeds 2.0

- returns FAIL when measured ratio exceeds 2.0
   - Expected: status equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("returns FAIL when measured ratio exceeds 2.0")
val status = classify_status("measured", 10.0, 2.5, 99.5)
expect(status).to_equal("FAIL")
```

</details>

#### returns FAIL when measured pixel_match below 95

- returns FAIL when measured pixel_match below 95
   - Expected: status equals `FAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("returns FAIL when measured pixel_match below 95")
val status = classify_status("measured", 10.0, 1.2, 90.0)
expect(status).to_equal("FAIL")
```

</details>

#### returns PASS for healthy measured data

- returns PASS for healthy measured data
   - Expected: status equals `PASS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("returns PASS for healthy measured data")
val status = classify_status("measured", 10.0, 1.2, 99.5)
expect(status).to_equal("PASS")
```

</details>

#### returns WARN when ratio between 1.5 and 2.0

- returns WARN when ratio between 1.5 and 2.0
   - Expected: status equals `WARN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("returns WARN when ratio between 1.5 and 2.0")
val status = classify_status("measured", 10.0, 1.8, 99.5)
expect(status).to_equal("WARN")
```

</details>

#### returns PENDING for synthetic regardless of timings

- returns PENDING for synthetic regardless of timings
   - Expected: status equals `PENDING`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("returns PENDING for synthetic regardless of timings")
val status = classify_status("synthetic", 5.0, 0.8, 100.0)
expect(status).to_equal("PENDING")
```

</details>

### Chrome vs Simple — Report Output

#### prints full comparison report without error

- prints full comparison report without error
   - Expected: row_count(rows) equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("prints full comparison report without error")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Chrome vs Simple — Report Shape, Chrome vs Simple — Threshold Math, Chrome vs Simple — NFR 2B Compliance, Chrome vs Simple — classify_status, Chrome vs Simple — Report Output.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dcad5b40faee202849fb67507c550239158246a9d91c953060e85700f1a7057c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dcad5b40faee202849fb67507c550239158246a9d91c953060e85700f1a7057c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dcad5b40faee202849fb67507c550239158246a9d91c953060e85700f1a7057c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/05_perf/web_render_chrome/report_spec.spl
mirror: doc/06_spec/05_perf/web_render_chrome/report_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/web_render_chrome/report_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/web_render_chrome/report_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/web_render_chrome/report_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/web_render_chrome/report_spec.spl:318:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads all four fixture rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/web_render_chrome/report_spec.spl:324:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all rows have required fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/web_render_chrome/report_spec.spl:330:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all status values are valid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
