# Linux Hosted WM Pinned-Font and Event Specification

> This environmental scenario verifies the retained output of the canonical Linux live-window gate. The gate builds the production hosted entry with the pure-Simple compiler, opens a real winit window under X11, captures both the presented window and production framebuffer, and correlates host and internal WM events with newer rendered frames.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 0 | 0 | 3 |

<details>
<summary>Full Scenario Manual</summary>

# Linux Hosted WM Pinned-Font and Event Specification

This environmental scenario verifies the retained output of the canonical Linux live-window gate. The gate builds the production hosted entry with the pure-Simple compiler, opens a real winit window under X11, captures both the presented window and production framebuffer, and correlates host and internal WM events with newer rendered frames.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | BLOCKED — qualifying pure-Simple live-window run unavailable |
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
SIMPLE_BIN=/path/to/current/pure-simple \
sh scripts/check/check-linux-hosted-wm-live-window-evidence.shs
```

`SIMPLE_BIN` is required explicitly so an unrelated stale `bin/release`
artifact cannot become evidence. While the glyph oracle is `pending`, a
reviewer may run once with `LINUX_HOSTED_WM_CALIBRATE_GLYPH=1` to retain the
live crop and its reported hash. That calibration run always exits nonzero and
reports `glyph-oracle-calibration-only-*`; only a separately reviewed pinned
hash can admit a later live run.

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
├── terminal-title.deliberate-red.rgb
├── source.diff
├── native-source-manifest.sha256
├── native-source-manifest.after.sha256
├── snapshot.live.json
└── native-build.log
```

`window.png` is captured from the real X11 winit window. It is not an
offscreen or compatibility-renderer artifact. `framebuffer.live.ppm` is emitted
from the exact production pixel buffer that is handed to winit. The raw
`terminal-title.rgb` region must have the pinned checksum and must match the
same region extracted independently from `window.png`.

The admitted native-source manifest deterministically hashes every `.spl`
source under `src/os` and `src/lib`, the complete source roots available to
this entry-closure build. The wrapper captures it immediately before and after
native-build, rejects any change, and records the admitted manifest identity
and SHA-256. Git fallback additionally rejects tracked or untracked dirtiness
anywhere in those dependency roots.

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
The retained env records exact baseline/input/move/maximize/restore nonces
`1/2/3/4/5`, plus each phase's revision and frame checksum; the live gate rejects
missing values before reporting a pass.

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
- `glyph-oracle-pending-calibration-required-*` requires the explicit
  calibration opt-in before collecting a candidate.
- `glyph-oracle-calibration-only-*` retained a deliberately requested live
  candidate and completed the remaining checks. It is never a pass.
- `source-provenance-unavailable` means neither jj nor Git could bind the
  exact working-copy revision and source diff. It is never treated as clean.
- `explicit-simple-bin-required` means the caller did not select the current
  pure-Simple compiler explicitly.
- `native-source-manifest-changed-during-build` means an entry-closure input
  changed while native-build was running; the produced artifact is deleted.
- `simple-bin-changed-during-build` means the selected compiler changed while
  it was executing; the produced artifact is deleted.
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
- Trace the production font and event boundary
- Prepare one shared font batch for 2D and 3D
- Emit the selected font composite program and plan compilation
- Submit the boundary output to its canonical consumer
- Prove native submission and device readback
- Correlate visible pixels and input with one frame identity
- Reject disconnected stale or replayed evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 73 lines folded for reproduction.
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

step("Trace the production font and event boundary")
step("Prepare one shared font batch for 2D and 3D")
val draw_ir = file_read("src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl")
expect(draw_ir).to_contain("eng.select_font_identity(font_identity)")
expect(draw_ir).to_contain("eng.draw_text_with_advances")

step("Emit the selected font composite program and plan compilation")
val compositor = file_read("src/os/compositor/host_compositor_core.spl")
expect(compositor).to_contain("shared_wm_scene_draw_ir_composition_with_content")
expect(compositor).to_contain("executor.render_draw_ir_composition(composition, images)")

step("Submit the boundary output to its canonical consumer")
step("Prove native submission and device readback")
val evidence = file_read(EVIDENCE_PATH)
expect(evidence).to_contain("linux_hosted_wm_live_window_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_source_provenance_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_source_vcs=")
expect(evidence).to_contain("linux_hosted_wm_live_window_native_source_manifest_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_native_source_manifest_identity=native-build-entry-closure:")
expect(evidence).to_contain("linux_hosted_wm_live_window_native_source_manifest_sha256=")
expect(evidence).to_contain("linux_hosted_wm_live_window_frame_marker=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_framebuffer_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_live_window_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_glyph_crop_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_glyph_crop_live_match=true")
expect(evidence).to_contain("linux_hosted_wm_live_window_deliberate_red_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_compatibility_fallback_status=pass")
expect(evidence).to_contain("linux_hosted_wm_live_window_baseline_nonce=1")
expect(evidence).to_contain("linux_hosted_wm_live_window_input_nonce=2")
expect(evidence).to_contain("linux_hosted_wm_live_window_move_nonce=3")
expect(evidence).to_contain("linux_hosted_wm_live_window_maximize_nonce=4")
expect(evidence).to_contain("linux_hosted_wm_live_window_restore_nonce=5")
expect(evidence).to_contain("linux_hosted_wm_live_window_baseline_revision=")
expect(evidence).to_contain("linux_hosted_wm_live_window_input_revision=")
expect(evidence).to_contain("linux_hosted_wm_live_window_move_revision=")
expect(evidence).to_contain("linux_hosted_wm_live_window_maximize_revision=")
expect(evidence).to_contain("linux_hosted_wm_live_window_restore_revision=")
expect(evidence).to_contain("linux_hosted_wm_live_window_baseline_frame_checksum=")
expect(evidence).to_contain("linux_hosted_wm_live_window_input_frame_checksum=")
expect(evidence).to_contain("linux_hosted_wm_live_window_move_frame_checksum=")
expect(evidence).to_contain("linux_hosted_wm_live_window_maximize_frame_checksum=")
expect(evidence).to_contain("linux_hosted_wm_live_window_restore_frame_checksum=")

step("Correlate visible pixels and input with one frame identity")
step("Reject disconnected stale or replayed evidence")
val wrapper = file_read("scripts/check/check-linux-hosted-wm-live-window-evidence.shs")
expect(entry).to_contain("if command.valid and command.nonce > evidence_nonce:")
expect(entry).to_contain("evidence_nonce = command.nonce")
expect(wrapper).to_contain(".input.nonce == $issue_nonce")
expect(wrapper).to_contain("evidence-ack nonce=$issue_nonce phase=$issue_phase")
expect(wrapper).to_contain(".render.fallback_used == false")
expect(wrapper).to_contain("grep -Fq '[hosted-wm] draw-ir-rejected'")
expect(wrapper).to_contain("retain_phase baseline 1 snapshot-only")
expect(wrapper).to_contain("retain_phase input 2 snapshot-only")
expect(wrapper).to_contain("retain_phase move 3 snapshot-only")
expect(wrapper).to_contain("retain_phase maximize 4 applied")
expect(wrapper).to_contain("retain_phase restore 5 applied")
expect(wrapper).to_contain("[ \"$initial_revision\" -lt \"$input_revision\" ]")
expect(wrapper).to_contain("[ \"$input_revision\" -lt \"$move_revision\" ]")
expect(wrapper).to_contain("[ \"$move_revision\" -lt \"$max_revision\" ]")
expect(wrapper).to_contain("[ \"$max_revision\" -lt \"$restore_revision\" ]")
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

#### fails closed before live execution when its source contract is not explicit

- Run the wrapper source-contract self-test without a compiler default
- Reject silent Git-only provenance and stale release defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the wrapper source-contract self-test without a compiler default")
val command = "env -u SIMPLE_BIN BUILD_DIR=build/linux-hosted-wm-live-window-self-test sh scripts/check/check-linux-hosted-wm-live-window-evidence.shs --self-test"
val (stdout, stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)
expect(stderr).to_equal("")
expect(stdout).to_contain("linux_hosted_wm_live_window_self_test_status=pass")
expect(stdout).to_contain("linux_hosted_wm_live_window_self_test_source_provenance_status=pass")
expect(stdout).to_contain("linux_hosted_wm_live_window_self_test_simple_bin_default=explicit-required")
expect(stdout).to_contain("linux_hosted_wm_live_window_self_test_pending_glyph=calibration-required")
expect(stdout).to_contain("linux_hosted_wm_live_window_self_test_calibration_glyph=calibration-only")
expect(stdout).to_contain("linux_hosted_wm_live_window_self_test_native_source_manifest=stable")
expect(stdout).to_contain("linux_hosted_wm_live_window_self_test_git_dirty_dependency=rejected")

step("Reject silent Git-only provenance and stale release defaults")
val wrapper = file_read("scripts/check/check-linux-hosted-wm-live-window-evidence.shs")
expect(wrapper).to_contain("jj log -r @ --no-graph --no-pager")
expect(wrapper).to_contain("jj diff --git -r @ -- src/os src/lib")
expect(wrapper).to_contain("git_dependency_tree_clean || return 1")
expect(wrapper).to_contain("write_native_source_manifest \"$SOURCE_MANIFEST\"")
expect(wrapper).to_contain("write_native_source_manifest \"$SOURCE_MANIFEST_AFTER\"")
expect(wrapper).to_contain("emit fail source-provenance-unavailable")
expect(wrapper).to_contain("emit unavailable explicit-simple-bin-required")
expect(wrapper).to_contain("emit fail \"glyph-oracle-calibration-only-$glyph_sha\"")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 0 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 3 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/shared_multilingual_gpu_fonts.md`
- **Plan:** `doc/03_plan/sys_test/shared_multilingual_gpu_fonts.md`
- **Design:** `doc/05_design/shared_multilingual_gpu_fonts.md`
- **Research:** `doc/01_research/local/shared_multilingual_gpu_fonts.md`


</details>
