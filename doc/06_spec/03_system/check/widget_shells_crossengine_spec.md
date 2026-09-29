# Widget shells cross-engine comparator

> Validates the cross-engine widget-shell comparator (`scripts/check/compare-widget-crossengine.js`) that proves the NEW production widget fixtures render correctly by comparing the pure-Simple web engine (layout -> engine2d -> Metal) output against REAL Chrome and Electron rendering the SAME fixture HTML. The comparator encodes a side-by-side PNG per engine and computes a structural, no-blur comparison: theme color presence, non-text pixel agreement (glyph pixels excluded via the Chrome DOM text mask), and the panel color band edges. It only reports metrics; the check script (`scripts/check/check-widget-shells-crossengine-evidence.shs`) applies thresholds and derives a three-valued status (pass / divergent / fail).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Widget shells cross-engine comparator

Validates the cross-engine widget-shell comparator (`scripts/check/compare-widget-crossengine.js`) that proves the NEW production widget fixtures render correctly by comparing the pure-Simple web engine (layout -> engine2d -> Metal) output against REAL Chrome and Electron rendering the SAME fixture HTML. The comparator encodes a side-by-side PNG per engine and computes a structural, no-blur comparison: theme color presence, non-text pixel agreement (glyph pixels excluded via the Chrome DOM text mask), and the panel color band edges. It only reports metrics; the check script (`scripts/check/check-widget-shells-crossengine-evidence.shs`) applies thresholds and derives a three-valued status (pass / divergent / fail).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/widget_shells_crossengine_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the cross-engine widget-shell comparator
(`scripts/check/compare-widget-crossengine.js`) that proves the NEW production
widget fixtures render correctly by comparing the pure-Simple web engine
(layout -> engine2d -> Metal) output against REAL Chrome and Electron rendering
the SAME fixture HTML. The comparator encodes a side-by-side PNG per engine and
computes a structural, no-blur comparison: theme color presence, non-text pixel
agreement (glyph pixels excluded via the Chrome DOM text mask), and the panel
color band edges. It only reports metrics; the check script
(`scripts/check/check-widget-shells-crossengine-evidence.shs`) applies
thresholds and derives a three-valued status (pass / divergent / fail).

This spec exercises the comparator deterministically with fabricated ARGB
inputs so the structural math and the fail-closed paths are pinned without the
multi-minute GPU + browser pipeline.

**Plan:** doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Syntax

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/widget_shells_crossengine_spec.spl --mode=interpreter --clean --fail-fast
```

## Acceptance

- Identical ARGB across the three engines yields 100% non-text agreement, panel
  band edges that align, PNG artifacts on disk, and a comparator `status=pass`.
- A Simple bitmap whose panel geometry diverges from the two agreeing real
  engines is reported with low non-text agreement and non-matching panel band
  edges rather than hidden by tolerance.
- The comparator emits per-engine capture paths, byte sizes, and theme color
  counts for every fixture.
- A missing engine ARGB file fails closed with a specific reason.

## Scenarios

### Widget shells cross-engine comparator

#### reports full agreement when all three engines match

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports full agreement when all three engines match
   - Expected: code equals `0`
- Inspect matched non-text structure and artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports full agreement when all three engines match")
val root = "build/test-widget-crossengine-pass"
# panel gray #f5f5f5 fill on all three -> 0xFFF5F5F5 = 4294309365
val command = _run_command(root, "4294309365", "4294309365", "keep")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val env = file_read(root + "/out.env")
step("Inspect matched non-text structure and artifacts")
expect(env).to_contain("window_status=pass")
expect(env).to_contain("window_nontext_agree_simple_chrome_pct=100.00")
expect(env).to_contain("window_nontext_agree_chrome_electron_pct=100.00")
expect(env).to_contain("window_blur_or_tolerance_used=false")
expect(env).to_contain("window_geometry_panel_top_match_simple_chrome=true")
expect(env).to_contain("window_geometry_panel_bottom_match_simple_chrome=true")
expect(env).to_contain("window_simple_png_path=" + root + "/simple_window.png")
expect(env).to_contain("window_chrome_png_path=" + root + "/chrome_window.png")
expect(env).to_contain("window_electron_png_path=" + root + "/electron_window.png")
expect(env).to_contain("window_simple_panel_count=16")
expect(env).to_contain("window_chrome_panel_count=16")
expect(env).to_contain("window_simple_png_bytes=")
expect_not(env.contains("window_simple_png_bytes=0"))
```

</details>

#### surfaces Simple-vs-Chromium structural divergence without tolerance

- surfaces Simple-vs-Chromium structural divergence without tolerance
   - Expected: code equals `0`
- Confirm divergence is measured, not blurred away


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("surfaces Simple-vs-Chromium structural divergence without tolerance")
val root = "build/test-widget-crossengine-divergent"
# Simple fills white #ffffff (0xFFFFFFFF=4294967295); real engines fill
# panel gray (0xFFF5F5F5=4294309365) -> no panel band in Simple, zero
# non-text agreement while the two real engines still agree fully.
val command = _run_command(root, "4294967295", "4294309365", "keep")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val env = file_read(root + "/out.env")
step("Confirm divergence is measured, not blurred away")
expect(env).to_contain("window_nontext_agree_simple_chrome_pct=0.00")
expect(env).to_contain("window_nontext_agree_chrome_electron_pct=100.00")
expect(env).to_contain("window_simple_panel_count=0")
expect(env).to_contain("window_chrome_panel_count=16")
expect(env).to_contain("window_geometry_panel_top_match_simple_chrome=false")
```

</details>

#### fails closed when an engine ARGB file is missing

- fails closed when an engine ARGB file is missing
   - Expected: code equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed when an engine ARGB file is missing")
val root = "build/test-widget-crossengine-missing"
val command = _run_command(root, "4294769916", "4294769916", "drop")
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(1)

val env = file_read(root + "/out.env")
expect(env).to_contain("window_status=fail")
expect(env).to_contain("window_reason=missing-simple-argb")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md`
- **Design:** `doc/07_guide/tooling/renderdoc_capture_infra.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e38293540505458672aebf207c55379b6b54aea3f878931ecb095971e6746c7e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e38293540505458672aebf207c55379b6b54aea3f878931ecb095971e6746c7e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e38293540505458672aebf207c55379b6b54aea3f878931ecb095971e6746c7e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/check/widget_shells_crossengine_spec.spl
mirror: doc/06_spec/03_system/check/widget_shells_crossengine_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/widget_shells_crossengine_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/widget_shells_crossengine_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/widget_shells_crossengine_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/widget_shells_crossengine_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports full agreement when all three engines match' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/widget_shells_crossengine_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'surfaces Simple-vs-Chromium structural divergence without tolerance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/widget_shells_crossengine_spec.spl:121:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when an engine ARGB file is missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
