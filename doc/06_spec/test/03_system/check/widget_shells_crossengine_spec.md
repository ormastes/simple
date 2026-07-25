# Widget shells cross-engine comparator

> Validates the cross-engine widget-shell comparator (`scripts/check/compare-widget-crossengine.js`) that proves the NEW production widget fixtures render correctly by comparing the pure-Simple web engine (layout -> engine2d -> Metal) output against REAL Chrome and Electron rendering the SAME fixture HTML. The comparator encodes a side-by-side PNG per engine and computes a structural, no-blur comparison: theme color presence, non-text pixel agreement (glyph pixels excluded via the Chrome DOM text mask), and the panel color band edges. It only reports metrics; the check script (`scripts/check/check-widget-shells-crossengine-evidence.shs`) applies thresholds and derives a three-valued status (pass / divergent / fail).

<!-- sdn-diagram:id=widget_shells_crossengine_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=widget_shells_crossengine_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

widget_shells_crossengine_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=widget_shells_crossengine_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

- Inspect matched non-text structure and artifacts
- expect not


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Confirm divergence is measured, not blurred away


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Plan:** [doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md](doc/03_plan/ui/tui/production_gui_web_renderer_parity_hardening.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
