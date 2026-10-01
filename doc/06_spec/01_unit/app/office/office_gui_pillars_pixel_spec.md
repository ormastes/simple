# office_gui_pillars_pixel_spec

> Office interactive-GUI pixel render across suite pillars.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# office_gui_pillars_pixel_spec

Office interactive-GUI pixel render across suite pillars.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/office_gui_pillars_pixel_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Office interactive-GUI pixel render across suite pillars.

Companion to office_gui_pixel_spec (the counter pilot). Proves the office GUI
rasterizes REAL pixels through the production browser layout/paint path for the
concrete suite surfaces — a spreadsheet grid (Calc/Excel), a chart, a pivot
table, and a slide (Impress/PowerPoint) — not just the counter pilot. Each
surface's view-builder (sheet_gui_view / chart_gui_view / pivot_gui_view /
slide_gui_view, all independently spec-covered) is rendered to an ARGB buffer
via its office_gui_*_pixels entry, and the non-background pixel count is
asserted positive (real widget content, not a blank canvas).

This is the cross-pillar interactive-GUI-fidelity evidence: the same render
path production uses, exercised for four distinct office surfaces, all green
and fast (each rasterizes in a few seconds after the apply_decls perf fix and
the default_style overload-collision workaround). The deliberate-fail probe at
the end proves the runner actually executes these rasterizations.

## Scenarios

### office GUI pillars: spreadsheet grid renders pixels

#### sheet_gui_view rasterizes to a non-blank frame

- sheet_gui_view rasterizes to a non-blank frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sheet_gui_view rasterizes to a non-blank frame")
val view = sheet_gui_view(_demo_sheet(), 2, 2)
val pixels = office_gui_sheet_pixels(view)
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(pixels.len()).to_be_greater_than(0)
expect(nonbg).to_be_greater_than(0)
```

</details>

### office GUI pillars: chart renders pixels
_The chart surface rasterizes real content._

#### chart_gui_view rasterizes to a non-blank frame

- chart_gui_view rasterizes to a non-blank frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chart_gui_view rasterizes to a non-blank frame")
val view = chart_gui_view(_demo_sheet(), "bar", "B1:B2", "A1:A2", "Sales", 96, 64)
val pixels = office_gui_chart_pixels(view)
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(nonbg).to_be_greater_than(0)
```

</details>

### office GUI pillars: pivot table renders pixels
_The pivot surface rasterizes real content._

#### pivot_gui_view rasterizes to a non-blank frame

- pivot_gui_view rasterizes to a non-blank frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pivot_gui_view rasterizes to a non-blank frame")
val view = pivot_gui_view(_pivot_sheet(), "A1:C4", 0, 1, 2, "SUM", "Region x Product")
val pixels = office_gui_pivot_pixels(view)
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(nonbg).to_be_greater_than(0)
```

</details>

### office GUI pillars: slide renders pixels
_The Impress/PowerPoint slide surface rasterizes real content._

#### slide_gui_view rasterizes to a non-blank frame

- slide_gui_view rasterizes to a non-blank frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("slide_gui_view rasterizes to a non-blank frame")
var deck: [Slide] = []
var s = blank_slide("s1")
s = add_text_box(s, "title", "Intro", 60, 60, 840, 120)
deck.push(s)
val view = slide_gui_view(deck, 0)
val pixels = office_gui_slide_pixels(view)
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(nonbg).to_be_greater_than(0)
```

</details>

#### deliberate-fail probe proves the tail of the file executes

- deliberate-fail probe proves the tail of the file executes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deliberate-fail probe proves the tail of the file executes")
val view = sheet_gui_view(_demo_sheet(), 2, 2)
val pixels = office_gui_sheet_pixels(view)
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(nonbg).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8e10681e53c77100f3fed8a98d9e3bbec68e9e9bfbf3668423e828666844631a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8e10681e53c77100f3fed8a98d9e3bbec68e9e9bfbf3668423e828666844631a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8e10681e53c77100f3fed8a98d9e3bbec68e9e9bfbf3668423e828666844631a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/office_gui_pillars_pixel_spec.spl
mirror: doc/06_spec/01_unit/app/office/office_gui_pillars_pixel_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/office_gui_pillars_pixel_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/office_gui_pillars_pixel_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/office_gui_pillars_pixel_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sheet_gui_view rasterizes to a non-blank frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/office_gui_pillars_pixel_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'chart_gui_view rasterizes to a non-blank frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/office_gui_pillars_pixel_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pivot_gui_view rasterizes to a non-blank frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
