# Reftest Runner Specification

> Tests covering Acid2 PixelGrid — basics, Acid2 GoldenGuard — DesktopShell frame regressions, Acid2 WPT status — enum wrapper, Acid2ReftestRunner — reftest passes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reftest Runner Specification

## Scenarios

### Acid2 PixelGrid — basics

#### new allocates a transparent 16x16 grid

- new allocates a transparent 16x16 grid


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new allocates a transparent 16x16 grid")
val g = PixelGrid.new()
expect(g.width_of() == ACID2_GRID_WIDTH).to_be_true()
expect(g.height_of() == ACID2_GRID_HEIGHT).to_be_true()
expect(g.cell_count() == ACID2_GRID_CELLS).to_be_true()
expect(g.get(0, 0) == ACID2_PIXEL_TRANSPARENT).to_be_true()
```

</details>

#### filled paints every cell with the palette index

- filled paints every cell with the palette index


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filled paints every cell with the palette index")
val g = PixelGrid.filled(ACID2_PIXEL_WHITE)
expect(g.get(0, 0) == ACID2_PIXEL_WHITE).to_be_true()
expect(g.get(15, 15) == ACID2_PIXEL_WHITE).to_be_true()
expect(g.count_colour(ACID2_PIXEL_WHITE) == ACID2_GRID_CELLS).to_be_true()
```

</details>

#### set + get round-trip a pixel

- set + get round-trip a pixel


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set + get round-trip a pixel")
var g = PixelGrid.new()
val ok = g.set(3, 4, ACID2_PIXEL_RED)
expect(ok).to_be_true()
expect(g.get(3, 4) == ACID2_PIXEL_RED).to_be_true()
```

</details>

#### set rejects out-of-bounds coordinates

- set rejects out-of-bounds coordinates


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set rejects out-of-bounds coordinates")
var g = PixelGrid.new()
expect(not g.set(-1, 0, ACID2_PIXEL_RED)).to_be_true()
expect(not g.set(0, 99, ACID2_PIXEL_RED)).to_be_true()
expect(g.get(-1, 0) == ACID2_PIXEL_TRANSPARENT).to_be_true()
```

</details>

#### fill_rect writes a clipped rectangle and reports cells touched

- fill_rect writes a clipped rectangle and reports cells touched


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fill_rect writes a clipped rectangle and reports cells touched")
var g = PixelGrid.new()
val n = g.fill_rect(0, 0, 3, 3, ACID2_PIXEL_SKIN)
expect(n == 16).to_be_true()
expect(g.get(0, 0) == ACID2_PIXEL_SKIN).to_be_true()
expect(g.get(3, 3) == ACID2_PIXEL_SKIN).to_be_true()
expect(g.get(4, 4) == ACID2_PIXEL_TRANSPARENT).to_be_true()
```

</details>

#### stroke_rect paints only the border

- stroke_rect paints only the border


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stroke_rect paints only the border")
var g = PixelGrid.new()
val n = g.stroke_rect(0, 0, 4, 4, ACID2_PIXEL_BLACK)
expect(n > 0).to_be_true()
expect(g.get(0, 0) == ACID2_PIXEL_BLACK).to_be_true()
expect(g.get(4, 4) == ACID2_PIXEL_BLACK).to_be_true()
expect(g.get(2, 2) == ACID2_PIXEL_TRANSPARENT).to_be_true()
```

</details>

#### equals reports identical grids as equal

- equals reports identical grids as equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("equals reports identical grids as equal")
val a = PixelGrid.filled(ACID2_PIXEL_WHITE)
val b = PixelGrid.filled(ACID2_PIXEL_WHITE)
expect(a.equals(b)).to_be_true()
expect(a.diff_count(b) == 0).to_be_true()
```

</details>

#### diff_count counts differing cells

- diff_count counts differing cells


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("diff_count counts differing cells")
var a = PixelGrid.filled(ACID2_PIXEL_WHITE)
var b = PixelGrid.filled(ACID2_PIXEL_WHITE)
b.set(1, 1, ACID2_PIXEL_RED)
b.set(2, 2, ACID2_PIXEL_BLACK)
expect(a.diff_count(b) == 2).to_be_true()
expect(not a.equals(b)).to_be_true()
```

</details>

### Acid2 GoldenGuard — DesktopShell frame regressions
_Registry that tracks DesktopShell golden frames across a reftest pass._

#### starts empty with no regressions

- starts empty with no regressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts empty with no regressions")
val g = GoldenGuard.new()
expect(g.is_empty()).to_be_true()
expect(g.count() == 0).to_be_true()
expect(g.no_regressions()).to_be_true()
expect(g.regression_count() == 0).to_be_true()
```

</details>

#### register stores a golden frame by name

- register stores a golden frame by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("register stores a golden frame by name")
var g = GoldenGuard.new()
val ok = g.register("shell.titlebar", PixelGrid.filled(ACID2_PIXEL_WHITE))
expect(ok).to_be_true()
expect(g.has_golden("shell.titlebar")).to_be_true()
expect(g.count() == 1).to_be_true()
```

</details>

#### compare_frame returns MATCH for identical pixels

- compare_frame returns MATCH for identical pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compare_frame returns MATCH for identical pixels")
var g = GoldenGuard.new()
g.register("shell.taskbar", PixelGrid.filled(ACID2_PIXEL_WHITE))
val v = g.compare_frame("shell.taskbar", PixelGrid.filled(ACID2_PIXEL_WHITE))
expect(v.is_match()).to_be_true()
expect(v.diff_pixels_of() == 0).to_be_true()
expect(g.no_regressions()).to_be_true()
expect(g.match_calls_of() == 1).to_be_true()
```

</details>

#### compare_frame returns DRIFTED and logs the name on mismatch

- compare_frame returns DRIFTED and logs the name on mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compare_frame returns DRIFTED and logs the name on mismatch")
var g = GoldenGuard.new()
g.register("shell.titlebar", PixelGrid.filled(ACID2_PIXEL_WHITE))
var candidate = PixelGrid.filled(ACID2_PIXEL_WHITE)
candidate.set(0, 0, ACID2_PIXEL_RED)
val v = g.compare_frame("shell.titlebar", candidate)
expect(v.is_drifted()).to_be_true()
expect(v.is_regression()).to_be_true()
expect(v.diff_pixels_of() == 1).to_be_true()
expect(not g.no_regressions()).to_be_true()
expect(g.regression_count() == 1).to_be_true()
```

</details>

#### compare_frame returns UNKNOWN for an unregistered name

- compare_frame returns UNKNOWN for an unregistered name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compare_frame returns UNKNOWN for an unregistered name")
var g = GoldenGuard.new()
val v = g.compare_frame("shell.ghost", PixelGrid.new())
expect(v.is_unknown()).to_be_true()
expect(v.code_of() == GOLDEN_VERDICT_UNKNOWN).to_be_true()
expect(g.no_regressions()).to_be_true()
```

</details>

#### reset_pass clears per-pass counters but keeps registered frames

- reset_pass clears per-pass counters but keeps registered frames


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reset_pass clears per-pass counters but keeps registered frames")
var g = GoldenGuard.new()
g.register("a", PixelGrid.filled(ACID2_PIXEL_WHITE))
var bad = PixelGrid.filled(ACID2_PIXEL_WHITE)
bad.set(5, 5, ACID2_PIXEL_BLACK)
g.compare_frame("a", bad)
expect(g.regression_count() == 1).to_be_true()
g.reset_pass()
expect(g.regression_count() == 0).to_be_true()
expect(g.has_golden("a")).to_be_true()
```

</details>

#### verdict labels round-trip

- verdict labels round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verdict labels round-trip")
val m = GoldenVerdict.match()
val d = GoldenVerdict.drifted(7)
val s = GoldenVerdict.size_diff(99)
val u = GoldenVerdict.unknown()
expect(m.label() == "match").to_be_true()
expect(d.label() == "drifted").to_be_true()
expect(s.label() == "size_diff").to_be_true()
expect(u.label() == "unknown").to_be_true()
```

</details>

### Acid2 WPT status — enum wrapper
_Small enum wrapper matching the WPT report status column._

#### constructors build the three WPT rows

- constructors build the three WPT rows


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constructors build the three WPT rows")
val u = Acid2WptStatus.unsupported()
val f = Acid2WptStatus.failed()
val s = Acid2WptStatus.supported()
expect(u.is_unsupported()).to_be_true()
expect(f.is_failed()).to_be_true()
expect(s.is_supported()).to_be_true()
```

</details>

#### labels match the WPT report strings

- labels match the WPT report strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("labels match the WPT report strings")
expect(Acid2WptStatus.supported().label() == "SUPPORTED").to_be_true()
expect(Acid2WptStatus.unsupported().label() == "UNSUPPORTED").to_be_true()
expect(Acid2WptStatus.failed().label() == "FAILED").to_be_true()
```

</details>

#### status codes match the exported constants

- status codes match the exported constants


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("status codes match the exported constants")
expect(Acid2WptStatus.supported().code_of() == ACID2_STATUS_SUPPORTED).to_be_true()
expect(Acid2WptStatus.failed().code_of() == ACID2_STATUS_FAILED).to_be_true()
expect(Acid2WptStatus.unsupported().code_of() == ACID2_STATUS_UNSUPPORTED).to_be_true()
```

</details>

### Acid2ReftestRunner — reftest passes
_M12 acceptance harness: reftest pixels + DesktopShell golden guard._

#### new creates an empty runner

- new creates an empty runner


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("new creates an empty runner")
val r = Acid2ReftestRunner.new()
expect(r.pass_count_of() == 0).to_be_true()
expect(r.last_diff_of() == 0).to_be_true()
```

</details>

#### identical reference + rendered grids flip WPT to SUPPORTED

- identical reference + rendered grids flip WPT to SUPPORTED


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("identical reference + rendered grids flip WPT to SUPPORTED")
var r = Acid2ReftestRunner.new()
r.load_reference(PixelGrid.filled(ACID2_PIXEL_WHITE))
r.load_rendered(PixelGrid.filled(ACID2_PIXEL_WHITE))
expect(r.pixels_match()).to_be_true()
val report = r.run_pass()
expect(report.status().is_supported()).to_be_true()
expect(report.diff_pixels_of() == 0).to_be_true()
expect(report.is_supported()).to_be_true()
expect(r.pass_count_of() == 1).to_be_true()
```

</details>

#### pixel mismatch flips the report to FAILED

- pixel mismatch flips the report to FAILED


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pixel mismatch flips the report to FAILED")
var r = Acid2ReftestRunner.new()
var ref = PixelGrid.filled(ACID2_PIXEL_WHITE)
var rendered = PixelGrid.filled(ACID2_PIXEL_WHITE)
rendered.set(1, 1, ACID2_PIXEL_RED)
r.load_reference(ref)
r.load_rendered(rendered)
val report = r.run_pass()
expect(report.status().is_failed()).to_be_true()
expect(report.diff_pixels_of() == 1).to_be_true()
expect(not report.is_supported()).to_be_true()
```

</details>

#### empty reference stays UNSUPPORTED

- empty reference stays UNSUPPORTED


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty reference stays UNSUPPORTED")
var r = Acid2ReftestRunner.new()
val report = r.run_pass()
expect(report.status().is_unsupported()).to_be_true()
```

</details>

#### DesktopShell golden regression forces SUPPORTED -> FAILED

- DesktopShell golden regression forces SUPPORTED -> FAILED


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("DesktopShell golden regression forces SUPPORTED -> FAILED")
var r = Acid2ReftestRunner.new()
r.load_reference(PixelGrid.filled(ACID2_PIXEL_WHITE))
r.load_rendered(PixelGrid.filled(ACID2_PIXEL_WHITE))
r.register_golden("shell.titlebar", PixelGrid.filled(ACID2_PIXEL_WHITE))
var bad = PixelGrid.filled(ACID2_PIXEL_WHITE)
bad.set(3, 3, ACID2_PIXEL_BLACK)
val v = r.compare_desktop("shell.titlebar", bad)
expect(v.is_drifted()).to_be_true()
val report = r.run_pass()
expect(report.golden_regressions_of() == 1).to_be_true()
expect(report.status().is_failed()).to_be_true()
expect(not report.is_supported()).to_be_true()
val names = report.regression_names_of()
expect(names.len() == 1).to_be_true()
```

</details>

#### full pass — Acid2 match + zero DesktopShell drift = SUPPORTED

- full pass — Acid2 match + zero DesktopShell drift = SUPPORTED


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full pass — Acid2 match + zero DesktopShell drift = SUPPORTED")
var r = Acid2ReftestRunner.new()
r.load_reference(PixelGrid.filled(ACID2_PIXEL_WHITE))
r.load_rendered(PixelGrid.filled(ACID2_PIXEL_WHITE))
r.register_golden("shell.titlebar", PixelGrid.filled(ACID2_PIXEL_WHITE))
r.register_golden("shell.taskbar",  PixelGrid.filled(ACID2_PIXEL_WHITE))
val v1 = r.compare_desktop("shell.titlebar", PixelGrid.filled(ACID2_PIXEL_WHITE))
val v2 = r.compare_desktop("shell.taskbar",  PixelGrid.filled(ACID2_PIXEL_WHITE))
expect(v1.is_match()).to_be_true()
expect(v2.is_match()).to_be_true()
val report = r.run_pass()
expect(report.is_supported()).to_be_true()
expect(report.golden_regressions_of() == 0).to_be_true()
expect(report.golden_matches_of() == 2).to_be_true()
expect(report.summary_line() == "acid2: SUPPORTED").to_be_true()
```

</details>

#### reset_pass clears per-pass state between runs

- reset_pass clears per-pass state between runs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reset_pass clears per-pass state between runs")
var r = Acid2ReftestRunner.new()
r.load_reference(PixelGrid.filled(ACID2_PIXEL_WHITE))
r.load_rendered(PixelGrid.filled(ACID2_PIXEL_BLACK))
r.run_pass()
expect(r.last_diff_of() > 0).to_be_true()
r.reset_pass()
expect(r.last_diff_of() == 0).to_be_true()
expect(r.guard_of().regression_count() == 0).to_be_true()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/ui.chromium.acid2/reftest_runner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Acid2 PixelGrid — basics, Acid2 GoldenGuard — DesktopShell frame regressions, Acid2 WPT status — enum wrapper, Acid2ReftestRunner — reftest passes.
- Acid2 PixelGrid — basics
- Acid2 GoldenGuard — DesktopShell frame regressions
- Acid2 WPT status — enum wrapper
- Acid2ReftestRunner — reftest passes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
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

- Canonical SPipe generation for source `6cc21e18bdea8f7132249086796f94e18b2f362ed73fb6faf8e585d7aea629c4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6cc21e18bdea8f7132249086796f94e18b2f362ed73fb6faf8e585d7aea629c4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6cc21e18bdea8f7132249086796f94e18b2f362ed73fb6faf8e585d7aea629c4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui.chromium.acid2/reftest_runner_spec.spl
mirror: doc/06_spec/unit/app/ui.chromium.acid2/reftest_runner_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui.chromium.acid2/reftest_runner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui.chromium.acid2/reftest_runner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui.chromium.acid2/reftest_runner_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'new allocates a transparent 16x16 grid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium.acid2/reftest_runner_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filled paints every cell with the palette index' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui.chromium.acid2/reftest_runner_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'set + get round-trip a pixel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
