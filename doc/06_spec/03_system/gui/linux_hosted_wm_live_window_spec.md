# Linux Hosted WM Pinned-Font and Event Specification

> This environmental scenario verifies the retained output of the canonical Linux live-window gate. The gate builds the production hosted entry with the pure-Simple compiler, opens a real winit window under X11, captures both the presented window and production framebuffer, and correlates host and internal WM events with newer rendered frames.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Linux Hosted WM Pinned-Font and Event Specification

This environmental scenario verifies the retained output of the canonical Linux live-window gate. The gate builds the production hosted entry with the pure-Simple compiler, opens a real winit window under X11, captures both the presented window and production framebuffer, and correlates host and internal WM events with newer rendered frames.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/shared_multilingual_gpu_fonts.md |
| Plan | doc/03_plan/sys_test/shared_multilingual_gpu_fonts.md |
| Design | doc/05_design/shared_multilingual_gpu_fonts.md |
| Research | doc/01_research/local/shared_multilingual_gpu_fonts.md |
| Source | `test/03_system/gui/linux_hosted_wm_live_window_spec.spl` |
| Updated | 2026-07-24 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This environmental scenario verifies the retained output of the canonical
Linux live-window gate. The gate builds the production hosted entry with the
pure-Simple compiler, opens a real winit window under X11, captures both the
presented window and production framebuffer, and correlates host and internal
WM events with newer rendered frames.

## Syntax

Run the live gate first:

```bash
BUILD_DIR=build/linux-hosted-wm-font-event-current \
REPORT_PATH=build/linux-hosted-wm-font-event-current/report.md \
sh scripts/check/check-linux-hosted-wm-live-window-evidence.shs
```

Then run this scenario with the pure-Simple self-hosted binary:

```bash
SIMPLE_LIB=src bin/release/x86_64-unknown-linux-gnu/simple test \
  test/03_system/gui/linux_hosted_wm_live_window_spec.spl \
  --mode=interpreter --clean --format json
```

The evidence is fail-closed. A compatibility-renderer retry, bitmap-default
font, missing live-window crop, nonmatching framebuffer crop, absent deliberate
red calibration, or event without a newer frame is a failure.

## Expected Evidence

The live command retains one evidence directory:

```text
build/linux-hosted-wm-font-event-current/
├── evidence.env
├── report.md
├── stdout.log
├── stderr.log
├── window.png
├── framebuffer.live.ppm
├── terminal-title.rgb
├── snapshot.live.json
└── native-build.log
```

`window.png` is captured from the real X11 winit window. It is not an
offscreen or compatibility-renderer artifact. `framebuffer.live.ppm` is emitted
from the exact production pixel buffer that is handed to winit. The raw
`terminal-title.rgb` region must have the pinned checksum and must match the
same region extracted independently from `window.png`.

The initial frame log must identify all production boundaries:

```text
renderer=engine2d-draw-ir
content=simple-web
route=shared-wm-scene-draw-ir
fallback=false
identity=<selected pinned face>
```

The event phase drives the real window with `xdotool`. Focus, pointer motion,
button input, and keyboard Tab must appear in the winit event log. The
production evidence command channel then snapshots the resulting compositor
state. Internal maximize and restore commands must update the focused window,
restore the exact pre-maximize window array, and advance the render revision.

## Absolute Glyph Oracle

The proof surface has one deterministic `Terminal` window at `(58, 76)`.
Shared WM title placement adds `(66, 8)`, so the gate extracts the fixed
`60x18+122+82` RGB region. The tracked SHA-256 binds that crop to the pinned
Noto Sans Mono asset. A second, deliberately corrupted crop must fail the same
hash comparison before the wrapper may report calibration success.

This crop is intentionally small. It proves the selected title glyphs without
depending on the taskbar clock, host time, window decoration, or unrelated
Simple Web body pixels.

## Event Correlation

The gate records strictly increasing revisions across:

1. the initial production frame;
2. native focus, pointer, button, and keyboard delivery;
3. internal maximize;
4. exact restore.

The outer host window is also moved to `(80, 60)`. The winit move marker and
snapshot surface geometry must agree. These checks distinguish an event sent
to the X server from an event actually consumed by the hosted WM.

## Failure Diagnostics

- `production-native-build-failed` means the pure-Simple compiler could not
  produce the hosted entry artifact. Inspect `native-build.log`; do not use the
  Rust seed as a substitute.
- `live-window-readiness-timeout` means the winit window or initial production
  evidence snapshot was not observed before the bounded deadline.
- `selected-font-identity-missing` means the frame used bitmap default text or
  never selected the pinned vector face.
- `glyph-oracle-pending-*` is the deliberate first-capture state used to pin a
  reviewed current-path crop. It is never a pass.
- `native-input-event-timeout` means X11 accepted the actions but the winit
  event stream did not report every required event.
- `live-font-or-event-evidence-incomplete` means at least one explicit status
  row remained failed. Read `evidence.env`; no missing row is treated as a
  warning.

## Scope

This scenario covers Linux hosted WM only. SimpleOS QEMU framebuffer proof is
owned by the separate guest lane. Engine3D HUD/world text, the offscreen hosted
capture helper, and compatibility renderers are not accepted here.

**Acceptance criteria:** AC-4, AC-6, AC-7, AC-8, AC-9
**Requirements:** doc/02_requirements/feature/shared_multilingual_gpu_fonts.md
**Plan:** doc/03_plan/sys_test/shared_multilingual_gpu_fonts.md
**Architecture:** doc/04_architecture/ui/simple_gui_stack.md
**Design:** doc/05_design/shared_multilingual_gpu_fonts.md
**Research:** doc/01_research/local/shared_multilingual_gpu_fonts.md

## Scenarios

### Linux hosted WM pinned font and correlated events

#### shows the pinned Terminal title through the production Engine2D frame

- Load the pinned multilingual font manifest
- Accept exact-face-bound simple-script shaping
- Prepare one shared font batch for 2D and 3D
- Emit the selected font composite program and plan compilation
- Prove native submission and device readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Load the pinned multilingual font manifest")
val entry = file_read("src/os/hosted/hosted_entry.spl")
val engine = file_read("src/os/compositor/compositor_engine2d.spl")
expect(entry).to_contain("font_provenance()")
expect(engine).to_contain("fn font_provenance() -> text:")
expect(engine).to_contain("current_font_identity()")

step("Accept exact-face-bound simple-script shaping")
val scene = file_read("src/lib/common/ui/window_scene_draw_ir.spl")
expect(scene).to_contain("resolve_font_metrics_with_language")
expect(scene).to_contain("draw_ir_text_resolved_font")

step("Prepare one shared font batch for 2D and 3D")
val draw_ir = file_read("src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl")
expect(draw_ir).to_contain("eng.select_font_identity(font_identity)")
expect(draw_ir).to_contain("eng.draw_text_with_advances")

step("Emit the selected font composite program and plan compilation")
val compositor = file_read("src/os/compositor/host_compositor_core.spl")
expect(compositor).to_contain("shared_wm_scene_draw_ir_composition_with_content")
expect(compositor).to_contain("executor.render_draw_ir_composition(composition, images)")

step("Prove native submission and device readback")
val evidence = file_read(EVIDENCE_PATH)
expect(evidence).to_contain("linux_hosted_wm_live_window_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_frame_marker=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_framebuffer_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_live_window_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_glyph_crop_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_glyph_crop_live_match=true")
expect(evidence).to_contain("linux_hosted_wm_live_window_deliberate_red_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_compatibility_fallback_status=pass")
```

</details>

#### delivers host and WM events to newer captured frames

- Build the production surface composition
- Submit the exact composition
- Deliver correlated focus keyboard and pointer events
- Capture backend and framebuffer evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build the production surface composition")
val entry = file_read("src/os/hosted/hosted_entry.spl")
expect(entry).to_contain("comp = _seed_live_proof_surface(comp)")
expect(entry).to_contain("comp.render_frame_engine2d(raster)")

step("Submit the exact composition")
expect(entry).to_contain("route=shared-wm-scene-draw-ir")
expect(entry).to_contain("fallback=false revision={comp.render_revision}")
expect(entry).to_contain("draw-ir-rejected evidence=fail-closed")

step("Deliver correlated focus keyboard and pointer events")
val evidence = file_read(EVIDENCE_PATH)
expect(evidence).to_contain("linux_hosted_wm_live_window_focus_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_pointer_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_keyboard_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_move_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_maximize_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_restore_status=pass")

step("Capture backend and framebuffer evidence")
expect(evidence).to_contain("linux_hosted_wm_live_window_frame_correlation_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_window_png=present")
expect(evidence).to_contain("linux_hosted_wm_live_window_framebuffer_ppm=present")
expect(evidence).to_contain("linux_hosted_wm_live_window_snapshot=present")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/shared_multilingual_gpu_fonts.md`
- **Plan:** `doc/03_plan/sys_test/shared_multilingual_gpu_fonts.md`
- **Design:** `doc/05_design/shared_multilingual_gpu_fonts.md`
- **Research:** `doc/01_research/local/shared_multilingual_gpu_fonts.md`


</details>
