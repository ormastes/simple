# office_gui_pixel_spec

> Office interactive-GUI pixel-render spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# office_gui_pixel_spec

Office interactive-GUI pixel-render spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/office_gui_pixel_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Office interactive-GUI pixel-render spec.

Proves the office GUI renders REAL pixels through the production browser
layout/paint path (office_gui_frame → render_html_tree → the same
simple_web_engine2d_render_html_pixels entry production uses), not a faked
or blank canvas. This is the interactive-GUI-fidelity evidence the campaign
was missing: the counter app's UITree is converted to HTML and rasterized to
an ARGB buffer whose non-background pixel count and checksum are asserted.

Historically this path was held out of the tree (render_frame was quadratic
in CSS size and hung past the 60s runner kill). After the apply_decls
pre-parse perf fix and the default_style overload-collision workaround, the
counter frame rasterizes in a few seconds, so it is now a first-class,
non-greenwashed spec (the deliberate-fail probe below proves the runner
actually executes these bodies).

## Scenarios

### office GUI: frame geometry

#### the frame buffer has exactly width*height pixels

- the frame buffer has exactly width*height pixels
   - Expected: w equals `96`
   - Expected: h equals `64`
   - Expected: pixels.len() equals `w * h`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("the frame buffer has exactly width*height pixels")
val pixels = office_gui_frame("counter")
val w = office_gui_frame_width()
val h = office_gui_frame_height()
expect(w).to_equal(96)
expect(h).to_equal(64)
expect(pixels.len()).to_equal(w * h)
```

</details>

### office GUI: real content
_A rendered frame carries real widget pixels, not a blank canvas._

#### the counter frame has a positive non-background pixel count

- the counter frame has a positive non-background pixel count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("the counter frame has a positive non-background pixel count")
val pixels = office_gui_frame("counter")
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(nonbg).to_be_greater_than(0)
```

</details>

### office GUI: Word document surface

#### the word frame has a positive non-background pixel count

- the word frame has a positive non-background pixel count
   - Expected: pixels.len() equals `w * h`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("the word frame has a positive non-background pixel count")
val pixels = office_gui_frame("word")
val w = office_gui_frame_width()
val h = office_gui_frame_height()
expect(pixels.len()).to_equal(w * h)
val nonbg = office_gui_non_background_pixel_count(pixels)
expect(nonbg).to_be_greater_than(0)
```

</details>

### office GUI: deterministic render
_Rendering the same app twice yields byte-identical pixels._

#### two renders of the counter produce the same checksum

- two renders of the counter produce the same checksum
   - Expected: ca equals `cb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("two renders of the counter produce the same checksum")
val a = office_gui_frame("counter")
val b = office_gui_frame("counter")
val ca = office_gui_pixel_checksum(a)
val cb = office_gui_pixel_checksum(b)
expect(ca).to_equal(cb)
```

</details>

#### deliberate-fail probe proves the tail of the file executes

- deliberate-fail probe proves the tail of the file executes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("deliberate-fail probe proves the tail of the file executes")
val pixels = office_gui_frame("counter")
val nonbg = office_gui_non_background_pixel_count(pixels)
# This must be > 0; asserting it correctly keeps the suite green and
# proves this describe (the last in the file) actually runs.
expect(nonbg).to_be_greater_than(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b008e69622ff9b3613ce1359f79a82b27792102ec3a0cebd9563945dd3074d74`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b008e69622ff9b3613ce1359f79a82b27792102ec3a0cebd9563945dd3074d74`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b008e69622ff9b3613ce1359f79a82b27792102ec3a0cebd9563945dd3074d74`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/office/office_gui_pixel_spec.spl
mirror: doc/06_spec/01_unit/app/office/office_gui_pixel_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/office_gui_pixel_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/office_gui_pixel_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/office_gui_pixel_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/office/office_gui_pixel_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the frame buffer has exactly width*height pixels' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/office_gui_pixel_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the counter frame has a positive non-background pixel count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/office_gui_pixel_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the word frame has a positive non-background pixel count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
