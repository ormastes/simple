# Chrome <-> Simple Component-Level Paint Differential

> Stage (5) of the per-component Chrome<->Simple renderer differential. Both

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chrome <-> Simple Component-Level Paint Differential

Stage (5) of the per-component Chrome<->Simple renderer differential. Both

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | In Progress |
| Source | `test/03_system/browser_engine/chrome_paint_differential_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Stage (5) of the per-component Chrome<->Simple renderer differential. Both
engines are fed the SAME HTML fixture and the SAME intermediate artifact is
extracted from each -- the engine's own **display list**, not a screenshot.
Chrome's side is `LayerTree.snapshotCommandLog`, the recorded `SkPicture` op
stream Blink's paint phase produced before rasterisation. Simple's side is
`simple_web_layout_render_html_draw_ir` -> `DrawIrComposition`. Comparing two
display lists isolates paint defects from raster, antialiasing and font-hinting
noise, which a pixel diff cannot do.

Audience: anyone changing `simple_web_html_layout_renderer_paint_layout.spl`,
`..._paint_primitives.spl`, or the Draw IR command emission feeding them.

## Scope and Preconditions

Requires a Chrome/Chromium executable and `node`. Both extractors and the differ
live in `tools/paint_diff/`. Extraction is done by the driver
`sh tools/paint_diff/run_paint_diff.shs` (about 10 minutes; it runs 18 separate
`bin/simple run` extractions, which cannot be nested inside `bin/simple test`).
This spec gates on the driver's retained evidence and is fail-closed on it:
missing evidence, evidence older than any fixture or extractor source, or a
chrome side that does not carry a real `Chrome/<version>` string all FAIL. There
is deliberately no "chrome absent, therefore pass" path.

## Primary Workflow

1. Run the driver.
2. Read `tools/paint_diff/out/summary.txt`.
3. Assert a NONZERO compared-op count on BOTH sides. A run that compared
   nothing is a failure, never a pass -- and an empty Skia command log is
   indistinguishable from perfect agreement, so this is the load-bearing gate.
4. Assert no fixture was BLOCKED.
5. Lock the fixtures that currently match Chrome exactly, so a paint regression
   in solid fills, nesting, stacking order, radius or alpha is caught at once.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Canonical paint op | `{kind, x, y, w, h, color, style, stroke_width?}` -- see `tools/paint_diff/CONTRACT.md` |
| Op expansion | Simple records one command per component carrying its style; the differ expands it into the primitives it implies, and flags the synthesised ones |
| EPS | 1 css px on geometry; colours compared EXACTLY as u32 (a paint colour is a decision, not a measurement) |

## Related Specifications

- [Paint differential I/O contract](../../../tools/paint_diff/CONTRACT.md)
- [Measured divergences and tool overview](../../../tools/paint_diff/README.md)
- [Layout differential (stage 3-4)](chrome_layout_differential_spec.spl)

## Evidence and Provenance

Measured against Google Chrome for Testing 151.0.7922.34, viewport 800x600,
deviceScaleFactor 1. Retained evidence: `tools/paint_diff/out/paint_report.json`
and `tools/paint_diff/out/summary.txt`. Baseline: 18 fixtures, 68 Chrome paint
ops vs 88 Simple paint ops, 16 recorded divergences.

## Recovery and Troubleshooting

`UNAVAILABLE: no chrome executable found` -- pass `--chrome <path>` or set
`PAINT_DIFF_CHROME`.

`chrome produced 0 paint ops` -- compositing is off. Chrome must be launched
WITHOUT `--disable-gpu`, and `LayerTree.enable` must be sent once after a first
real paint with the layer list read from the persistent
`LayerTree.layerTreeDidChange` event. Both mistakes yield an empty command log
that would otherwise read as a clean pass.

## Compatibility and Limitations

Chrome drops fully-occluded fills during paint-op recording, so a Simple fill
with no Chrome counterpart is not automatically a defect; the differ reports
both sides' values and leaves the judgement to the reader. Chrome folds element
opacity into the paint alpha while Simple carries `opacity` as a separate style
property, so opacity divergences surface as `fill-color`.

## Scenarios

### Chrome to Simple paint differential

#### has fresh paint-stage evidence produced against a real Chrome

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has fresh paint-stage evidence produced against a real Chrome
- The summary must exist and be newer than every fixture and extractor source
   - Expected: evidence_is_stale() is false
- A real Chrome must have produced the chrome side
   - Expected: version contains `Chrome/`
- Assert a nonzero compared-op count on the CHROME side
   - Expected: summary_i64("chrome_ops_compared") > 0 is true
- Assert a nonzero compared-op count on the SIMPLE side
   - Expected: summary_i64("simple_ops_compared") > 0 is true
- Assert no fixture was blocked
   - Expected: summary_i64("fixtures_blocked") equals `0`
- Assert every fixture was compared
   - Expected: summary_i64("fixtures_compared") equals `18`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has fresh paint-stage evidence produced against a real Chrome")
step("The summary must exist and be newer than every fixture and extractor source")
expect(evidence_is_stale()).to_equal(false)  # oracle: missing or stale evidence FAILS; run sh tools/paint_diff/run_paint_diff.shs
step("A real Chrome must have produced the chrome side")
val version = chrome_version()
expect(version.contains("Chrome/")).to_equal(true)  # oracle: chrome absent or extraction failed is a FAILURE, never a vacuous pass
step("Assert a nonzero compared-op count on the CHROME side")
expect(summary_i64("chrome_ops_compared") > 0).to_equal(true)  # oracle: an empty Skia command log reads exactly like agreement
step("Assert a nonzero compared-op count on the SIMPLE side")
expect(summary_i64("simple_ops_compared") > 0).to_equal(true)  # oracle: 0 findings over 0 ops is not a pass
step("Assert no fixture was blocked")
expect(summary_i64("fixtures_blocked")).to_equal(0)
step("Assert every fixture was compared")
expect(summary_i64("fixtures_compared")).to_equal(18)
```

</details>

#### exercises fills, strokes and text runs on both sides

- has fresh paint-stage evidence produced against a real Chrome
- The summary must exist and be newer than every fixture and extractor source
   - Expected: evidence_is_stale() is false
- A real Chrome must have produced the chrome side
   - Expected: version contains `Chrome/`
- Assert a nonzero compared-op count on the CHROME side
   - Expected: summary_i64("chrome_ops_compared") > 0 is true
- Assert a nonzero compared-op count on the SIMPLE side
   - Expected: summary_i64("simple_ops_compared") > 0 is true
- Assert no fixture was blocked
   - Expected: summary_i64("fixtures_blocked") equals `0`
- Assert every fixture was compared
   - Expected: summary_i64("fixtures_compared") equals `18`
- exercises fills, strokes and text runs on both sides
- Background fills must have been recorded by both engines
   - Expected: summary_i64("chrome_fill_ops") > 0 is true
   - Expected: summary_i64("simple_fill_ops") > 0 is true
- Text paint ops must have been recorded by both engines
   - Expected: summary_i64("chrome_text_ops") > 0 is true
   - Expected: summary_i64("simple_text_ops") > 0 is true
- Border strokes must have been recorded by Chrome, else the border oracle is vacuous
   - Expected: summary_i64("chrome_stroke_ops") > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has fresh paint-stage evidence produced against a real Chrome")
step("The summary must exist and be newer than every fixture and extractor source")
expect(evidence_is_stale()).to_equal(false)  # oracle: missing or stale evidence FAILS; run sh tools/paint_diff/run_paint_diff.shs
step("A real Chrome must have produced the chrome side")
val version = chrome_version()
expect(version.contains("Chrome/")).to_equal(true)  # oracle: chrome absent or extraction failed is a FAILURE, never a vacuous pass
step("Assert a nonzero compared-op count on the CHROME side")
expect(summary_i64("chrome_ops_compared") > 0).to_equal(true)  # oracle: an empty Skia command log reads exactly like agreement
step("Assert a nonzero compared-op count on the SIMPLE side")
expect(summary_i64("simple_ops_compared") > 0).to_equal(true)  # oracle: 0 findings over 0 ops is not a pass
step("Assert no fixture was blocked")
expect(summary_i64("fixtures_blocked")).to_equal(0)
step("Assert every fixture was compared")
expect(summary_i64("fixtures_compared")).to_equal(18)

# @req REQ-SSPEC-SYSTEM
step("exercises fills, strokes and text runs on both sides")
step("Background fills must have been recorded by both engines")
expect(summary_i64("chrome_fill_ops") > 0).to_equal(true)
expect(summary_i64("simple_fill_ops") > 0).to_equal(true)
step("Text paint ops must have been recorded by both engines")
expect(summary_i64("chrome_text_ops") > 0).to_equal(true)  # oracle: the text-paint oracle must have run
expect(summary_i64("simple_text_ops") > 0).to_equal(true)
step("Border strokes must have been recorded by Chrome, else the border oracle is vacuous")
expect(summary_i64("chrome_stroke_ops") > 0).to_equal(true)
```

</details>

#### keeps solid fills, nesting, stacking order, radius and alpha byte-exact against Chrome

- has fresh paint-stage evidence produced against a real Chrome
- The summary must exist and be newer than every fixture and extractor source
   - Expected: evidence_is_stale() is false
- A real Chrome must have produced the chrome side
   - Expected: version contains `Chrome/`
- Assert a nonzero compared-op count on the CHROME side
   - Expected: summary_i64("chrome_ops_compared") > 0 is true
- Assert a nonzero compared-op count on the SIMPLE side
   - Expected: summary_i64("simple_ops_compared") > 0 is true
- Assert no fixture was blocked
   - Expected: summary_i64("fixtures_blocked") equals `0`
- Assert every fixture was compared
   - Expected: summary_i64("fixtures_compared") equals `18`
- keeps solid fills, nesting, stacking order, radius and alpha byte-exact against Chrome
- Read the set of fixtures with zero findings
- Single and multiple solid fills must stay exact
   - Expected: clean contains `01_solid_fill`
   - Expected: clean contains `02_two_fills`
- Padding and nested fills must stay exact
   - Expected: clean contains `05_padding_fill`
   - Expected: clean contains `06_nested_fills`
- Text fill colour must stay exact
   - Expected: clean contains `07_text_color`
- Rounded fills, z-index paint order, transparency and rgba alpha must stay exact
   - Expected: clean contains `09_border_radius`
   - Expected: clean contains `11_overlap_zindex`
   - Expected: clean contains `12_transparent_bg`
   - Expected: clean contains `13_rgba_alpha`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has fresh paint-stage evidence produced against a real Chrome")
step("The summary must exist and be newer than every fixture and extractor source")
expect(evidence_is_stale()).to_equal(false)  # oracle: missing or stale evidence FAILS; run sh tools/paint_diff/run_paint_diff.shs
step("A real Chrome must have produced the chrome side")
val version = chrome_version()
expect(version.contains("Chrome/")).to_equal(true)  # oracle: chrome absent or extraction failed is a FAILURE, never a vacuous pass
step("Assert a nonzero compared-op count on the CHROME side")
expect(summary_i64("chrome_ops_compared") > 0).to_equal(true)  # oracle: an empty Skia command log reads exactly like agreement
step("Assert a nonzero compared-op count on the SIMPLE side")
expect(summary_i64("simple_ops_compared") > 0).to_equal(true)  # oracle: 0 findings over 0 ops is not a pass
step("Assert no fixture was blocked")
expect(summary_i64("fixtures_blocked")).to_equal(0)
step("Assert every fixture was compared")
expect(summary_i64("fixtures_compared")).to_equal(18)

# @req REQ-SSPEC-SYSTEM
step("keeps solid fills, nesting, stacking order, radius and alpha byte-exact against Chrome")
step("Read the set of fixtures with zero findings")
val clean = summary_value("clean_fixtures")
step("Single and multiple solid fills must stay exact")
expect(clean.contains("01_solid_fill")).to_equal(true)
expect(clean.contains("02_two_fills")).to_equal(true)
step("Padding and nested fills must stay exact")
expect(clean.contains("05_padding_fill")).to_equal(true)
expect(clean.contains("06_nested_fills")).to_equal(true)
step("Text fill colour must stay exact")
expect(clean.contains("07_text_color")).to_equal(true)
step("Rounded fills, z-index paint order, transparency and rgba alpha must stay exact")
expect(clean.contains("09_border_radius")).to_equal(true)
expect(clean.contains("11_overlap_zindex")).to_equal(true)
expect(clean.contains("12_transparent_bg")).to_equal(true)
expect(clean.contains("13_rgba_alpha")).to_equal(true)
```

</details>

#### holds the known paint divergences at or below the recorded baseline

- has fresh paint-stage evidence produced against a real Chrome
- The summary must exist and be newer than every fixture and extractor source
   - Expected: evidence_is_stale() is false
- A real Chrome must have produced the chrome side
   - Expected: version contains `Chrome/`
- Assert a nonzero compared-op count on the CHROME side
   - Expected: summary_i64("chrome_ops_compared") > 0 is true
- Assert a nonzero compared-op count on the SIMPLE side
   - Expected: summary_i64("simple_ops_compared") > 0 is true
- Assert no fixture was blocked
   - Expected: summary_i64("fixtures_blocked") equals `0`
- Assert every fixture was compared
   - Expected: summary_i64("fixtures_compared") equals `18`
- holds the known paint divergences at or below the recorded baseline
- Read the current finding count
- Absent evidence reads as -1 and must FAIL rather than satisfy the ratchet
   - Expected: findings >= 0 is true
- Nonzero ops must have been compared for the ratchet to mean anything
   - Expected: summary_i64("chrome_ops_compared") > 0 is true
   - Expected: summary_i64("simple_ops_compared") > 0 is true
- The baseline measured against Chrome 151.0.7922.34 is 16 findings; this may shrink but must not grow
   - Expected: findings <= 16 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has fresh paint-stage evidence produced against a real Chrome")
step("The summary must exist and be newer than every fixture and extractor source")
expect(evidence_is_stale()).to_equal(false)  # oracle: missing or stale evidence FAILS; run sh tools/paint_diff/run_paint_diff.shs
step("A real Chrome must have produced the chrome side")
val version = chrome_version()
expect(version.contains("Chrome/")).to_equal(true)  # oracle: chrome absent or extraction failed is a FAILURE, never a vacuous pass
step("Assert a nonzero compared-op count on the CHROME side")
expect(summary_i64("chrome_ops_compared") > 0).to_equal(true)  # oracle: an empty Skia command log reads exactly like agreement
step("Assert a nonzero compared-op count on the SIMPLE side")
expect(summary_i64("simple_ops_compared") > 0).to_equal(true)  # oracle: 0 findings over 0 ops is not a pass
step("Assert no fixture was blocked")
expect(summary_i64("fixtures_blocked")).to_equal(0)
step("Assert every fixture was compared")
expect(summary_i64("fixtures_compared")).to_equal(18)

# @req REQ-SSPEC-SYSTEM
step("holds the known paint divergences at or below the recorded baseline")
step("Read the current finding count")
val findings = summary_i64("findings_total")
step("Absent evidence reads as -1 and must FAIL rather than satisfy the ratchet")
expect(findings >= 0).to_equal(true)  # oracle: missing summary is not a pass
step("Nonzero ops must have been compared for the ratchet to mean anything")
expect(summary_i64("chrome_ops_compared") > 0).to_equal(true)  # oracle: no vacuous ratchet
expect(summary_i64("simple_ops_compared") > 0).to_equal(true)
step("The baseline measured against Chrome 151.0.7922.34 is 16 findings; this may shrink but must not grow")
expect(findings <= 16).to_equal(true)  # oracle: ratchet, see tools/paint_diff/README.md
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `138228f921e2246fbe8d0d190e8bfad12a7b835f853bbb5261f4799d8346aa33`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `138228f921e2246fbe8d0d190e8bfad12a7b835f853bbb5261f4799d8346aa33`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `138228f921e2246fbe8d0d190e8bfad12a7b835f853bbb5261f4799d8346aa33`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/browser_engine/chrome_paint_differential_spec.spl
mirror: doc/06_spec/03_system/browser_engine/chrome_paint_differential_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/browser_engine/chrome_paint_differential_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/03_system/browser_engine/chrome_paint_differential_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/browser_engine/chrome_paint_differential_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has fresh paint-stage evidence produced against a real Chrome' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/browser_engine/chrome_paint_differential_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exercises fills, strokes and text runs on both sides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/browser_engine/chrome_paint_differential_spec.spl:160:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps solid fills, nesting, stacking order, radius and alpha byte-exact against Chrome' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
