# Macos Gui Live Window Gate Source Specification

> Tests covering macOS GUI live-window gate source.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Macos Gui Live Window Gate Source Specification

## Scenarios

### macOS GUI live-window gate source

#### keeps launcher nudging outside the bounded evidence owner

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps launcher nudging outside the bounded evidence owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps launcher nudging outside the bounded evidence owner")
val source = rt_file_read_text("scripts/check/check-macos-gui-live-window-evidence.shs") ?? ""

expect(source).to_contain("SIMPLE_GUI_RUN_SKIP_NUDGE=1")
expect(source).to_contain("deadline=$(($(date +%s) + TIMEOUT_SECS))")
expect(source).to_contain("src/app/ui_shared_mdi/live_window.spl")
expect(source).to_contain("compile --format=smf")
expect(source).to_contain("live-artifact-compile-failed")
expect(source).to_contain("scripts/gui/macos-gui-run.shs \"$LIVE_LAUNCH_INPUT\"")
```

</details>

#### lets the macOS launcher consume compiled SMF artifacts

- lets the macOS launcher consume compiled SMF artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lets the macOS launcher consume compiled SMF artifacts")
val source = rt_file_read_text("scripts/gui/macos-gui-run.shs") ?? ""

expect(source).to_contain("expected a .spl source or compiled .smf artifact")
expect(source).to_contain("*.spl|*.smf")
expect(source).to_contain("--args run \"$program\"")
```

</details>

#### uses the real Simple Web renderer and winit host

- uses the real Simple Web renderer and winit host


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the real Simple Web renderer and winit host")
val source = rt_file_read_text("src/app/ui_shared_mdi/live_window.spl") ?? ""

expect(source).to_contain("simple_web_layout_render_html_software_pixels")
expect(source).to_contain("shared_mdi_terminal_window_html")
expect(source).to_contain("winit_window_new")
expect(source).to_contain("winit_present_rgba")
expect(source).to_contain("winit_wait_input(lp, 8)")
expect(source).to_contain("SIMPLE_GUI_EVENT_EVIDENCE_PATH")
expect(source).to_contain("native-event-evidence")
expect(source).to_contain("rgb(255,73,171)")
expect(source).to_contain("pointer_events = pointer_events + input.mouse_moves")
expect(source).to_contain("click_i < input.click_pressed.len() and click_i < input.click_buttons.len()")
expect(source).to_contain("shared_mdi_live_completed_click_target(input.click_buttons[click_i], input.click_pressed[click_i], click_x, click_y)")
expect(source).to_contain("if target != LIVE_CLICK_TARGET_NONE:\n                click_events = click_events + 1")
expect(source).to_contain("shared_mdi_live_events_complete(")
expect(source).to_contain("if render_failed:\n        return 4")
expect(source).to_contain("if not winit_present_rgba(win, LIVE_WIDTH.to_i64(), LIVE_HEIGHT.to_i64(), packed):")
expect(source).to_contain("if present_failed:\n        return 5")

val winit = rt_file_read_text("src/lib/nogc_sync_mut/io/window_winit.spl") ?? ""
expect(winit).to_contain("fn winit_present_rgba(win: WinitWindow, w: i64, h: i64, pixels: [i64]) -> bool:")
expect(winit).to_contain("return false\n    rt_winit_window_present_rgba(win.handle, w, h, pixels)")
```

</details>

#### escapes environment-derived iframe URLs before HTML composition

- escapes environment-derived iframe URLs before HTML composition


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes environment-derived iframe URLs before HTML composition")
val source = rt_file_read_text("src/app/ui_shared_mdi/main.spl") ?? ""

expect(source).to_contain("shared_mdi_browser_iframe_html(browser_url)")
```

</details>

#### counts pointer events explicitly in both winit input drains

- counts pointer events explicitly in both winit input drains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts pointer events explicitly in both winit input drains")
val source = rt_file_read_text("src/lib/nogc_sync_mut/io/window_winit.spl") ?? ""

expect(source).to_contain("mouse_moves: i64")
expect(source).to_contain("mouse_moves = mouse_moves + 1")
expect(source).to_contain("mouse_x: mouse_x, mouse_y: mouse_y, mouse_moves: mouse_moves")
```

</details>

#### measures a completion-only event-counter color in the captured frame

- measures a completion-only event-counter color in the captured frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures a completion-only event-counter color in the captured frame")
val measure = rt_file_read_text("scripts/check/measure_macos_gui_live_window_bmp.spl") ?? ""

expect(measure).to_contain("near_color(r, g, b, 255, 73, 171, 2)")
expect(measure).to_contain("completed_event_counter_pixels = completed_event_counter_pixels + 1")
expect(measure).to_contain("completed_event_counter_pixels.to_string()")
```

</details>

#### requires focused keyboard pointer and click delivery evidence

- requires focused keyboard pointer and click delivery evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires focused keyboard pointer and click delivery evidence")
val source = rt_file_read_text("scripts/check/check-macos-gui-live-window-evidence.shs") ?? ""

expect(source).to_contain("event-focus-failed")
expect(source).to_contain("event-keyboard-missing")
expect(source).to_contain("event-pointer-missing")
expect(source).to_contain("event-click-missing")
expect(source).to_contain("event-titlebar-control-click-missing")
expect(source).to_contain("event-body-control-click-missing")
expect(source).to_contain("click at {wx + 500, wy + 95}")
expect(source).to_contain("click at {wx + 80, wy + 235}")
expect(source).to_contain("capture-completed-event-counters-missing")
expect(source).to_contain("macos_gui_live_window_evidence_completed_event_counter_pixels")
expect(source).to_contain("SIMPLE_GUI_EVENT_EVIDENCE_PATH")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/scripts/macos_gui_live_window_gate_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering macOS GUI live-window gate source.
- macOS GUI live-window gate source

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `56c5d3810d0c9fc147bbc52f945dec15647286d3ccd4800117599ec47a3e06bf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `56c5d3810d0c9fc147bbc52f945dec15647286d3ccd4800117599ec47a3e06bf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `56c5d3810d0c9fc147bbc52f945dec15647286d3ccd4800117599ec47a3e06bf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/scripts/macos_gui_live_window_gate_source_spec.spl
mirror: doc/06_spec/01_unit/scripts/macos_gui_live_window_gate_source_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/scripts/macos_gui_live_window_gate_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/scripts/macos_gui_live_window_gate_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/scripts/macos_gui_live_window_gate_source_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps launcher nudging outside the bounded evidence owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/scripts/macos_gui_live_window_gate_source_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lets the macOS launcher consume compiled SMF artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/scripts/macos_gui_live_window_gate_source_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the real Simple Web renderer and winit host' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
