# Editor Gui Sdl Specification

> Tests covering Editor GUI SDL Bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Gui Sdl Specification

## Scenarios

### Editor GUI SDL Bridge

#### gui_sdl_bridge.spl exists and is non-empty

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- gui_sdl_bridge.spl exists and is non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gui_sdl_bridge.spl exists and is non-empty")
# Was `to_contain("gui_sdl_bridge")`, which matched only the file-header
# comment naming the module — true even of an otherwise empty file.
val src = file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect(src.len()).to_be_greater_than(0)
expect (src).to_contain("fn gui_sdl_")
```

</details>

#### gui_sdl_init function declared

- gui_sdl_init function declared


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gui_sdl_init function declared")
val src = file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).to_contain("fn gui_sdl_init(")
```

</details>

#### gui_sdl_render_text_block function declared

- gui_sdl_render_text_block function declared


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gui_sdl_render_text_block function declared")
val src = file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).to_contain("fn gui_sdl_render_text_block(")
```

</details>

#### gui_sdl_present_frame function declared

- gui_sdl_present_frame function declared


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gui_sdl_present_frame function declared")
val src = file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).to_contain("fn gui_sdl_present_frame(")
```

</details>

#### legacy SDL GUI font route source contract uses Draw IR and closes Engine2D

- legacy SDL GUI font route source contract uses Draw IR and closes Engine2D


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("legacy SDL GUI font route source contract uses Draw IR and closes Engine2D")
val src = file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).to_contain("fn gui_sdl_frame_draw_ir(")
expect (src).to_contain("resolve_font_metrics(candidate.family")
expect (src).to_contain("simpleos_default_font_asset_candidate()")
expect (src).to_contain("metrics.identity")
expect (src).to_contain("metrics.glyph_run")
expect (src).to_contain("draw_ir_text_resolved_font(")
expect (src).to_contain("draw_ir_text_shaped_font(")
expect (src).to_contain("Engine2D.create_offscreen(")
expect (src).to_contain("engine2d_draw_ir_adv_composition(")
expect (src).to_contain("engine.shutdown()")
expect (src).to_contain("result.skipped_command_count != 0")
expect (src).to_contain("color_r(pixel).to_i64()")
expect (src).to_contain("color_a(pixel).to_i64()")
expect (src).to_contain("_sdl_engine_pixels(result.pixels)")
expect (src).to_not_contain("placeholder glyph")
expect (src).to_not_contain("_sdl_fill_rect(")
```

</details>

#### gui_sdl_poll function declared

- gui_sdl_poll function declared


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gui_sdl_poll function declared")
val src = file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).to_contain("fn gui_sdl_poll(")
```

</details>

#### gui_sdl_poll maps printable key symbols to text

- gui_sdl_poll maps printable key symbols to text


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gui_sdl_poll maps printable key symbols to text")
val src = file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).to_contain("char_from_code(sym)")
expect (src).to_contain("data: \"Enter\"")
expect (src).to_contain("data: \"Backspace\"")
```

</details>

#### gui_sdl_poll maps modifier key chords

- gui_sdl_poll maps modifier key chords


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gui_sdl_poll maps modifier key chords")
val src = file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).to_contain("rt_sdl_event_key_mod()")
expect (src).to_contain("\"Ctrl+\" + letter")
expect (src).to_contain("\"Ctrl+Shift+\" + letter")
expect (src).to_contain("Shift+Alt+Right")
expect (src).to_contain("Shift+Alt+Left")
```

</details>

#### gui_sdl_poll maps text input events

- gui_sdl_poll maps text input events


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gui_sdl_poll maps text input events")
val src = file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).to_contain("extern fn rt_sdl_event_text() -> text")
expect (src).to_contain("if ev == 9:")
expect (src).to_contain("GuiEvent(kind: \"text\", data: rt_sdl_event_text())")
```

</details>

#### gui_sdl_poll maps window resize and focus events

- gui_sdl_poll maps window resize and focus events


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gui_sdl_poll maps window resize and focus events")
val src = file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).to_contain("rt_sdl_event_window_event_id()")
expect (src).to_contain("GuiEvent(kind: \"resize\"")
expect (src).to_contain("GuiEvent(kind: \"focus\"")
expect (src).to_contain("GuiEvent(kind: \"blur\"")
```

</details>

#### rt_sdl_create_window extern declared

- rt_sdl_create_window extern declared


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rt_sdl_create_window extern declared")
val src = file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).to_contain("extern fn rt_sdl_create_window(")
```

</details>

#### rt_sdl_present_rgba extern declared

- rt_sdl_present_rgba extern declared


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rt_sdl_present_rgba extern declared")
val src = file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).to_contain("extern fn rt_sdl_present_rgba(")
```

</details>

#### rt_sdl_poll_event extern declared

- rt_sdl_poll_event extern declared


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rt_sdl_poll_event extern declared")
val src = file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).to_contain("extern fn rt_sdl_poll_event(")
```

</details>

#### gui_shell_present_frame_sdl added to gui_shell.spl

- gui_shell_present_frame_sdl added to gui_shell.spl


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gui_shell_present_frame_sdl added to gui_shell.spl")
val src = file_read_text("src/app/editor/gui_shell.spl") ?? ""
expect (src).to_contain("fn gui_shell_present_frame_sdl(")
```

</details>

#### gui_shell_present_frame_sdl delegates to gui_sdl_present_frame

- gui_shell_present_frame_sdl delegates to gui_sdl_present_frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gui_shell_present_frame_sdl delegates to gui_sdl_present_frame")
val src = file_read_text("src/app/editor/gui_shell.spl") ?? ""
expect (src).to_contain("gui_sdl_present_frame(window, frame)")
```

</details>

<details>
<summary>Advanced: gui shell has SDL run loop with runtime event polling</summary>

#### gui shell has SDL run loop with runtime event polling

- gui shell has SDL run loop with runtime event polling


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gui shell has SDL run loop with runtime event polling")
val src = file_read_text("src/app/editor/gui_shell.spl") ?? ""
expect (src).to_contain("fn gui_shell_run_sdl(session: EditSession)")
expect (src).to_contain("gui_sdl_init(state.config.window_title")
expect (src).to_contain("gui_shell_poll_event_sdl()")
expect (src).to_contain("gui_sdl_shutdown(window)")
```

</details>


</details>

#### gui shell routes SDL text and clipboard shortcuts

- gui shell routes SDL text and clipboard shortcuts


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gui shell routes SDL text and clipboard shortcuts")
val src = file_read_text("src/app/editor/gui_shell.spl") ?? ""
expect (src).to_contain("elif event_kind == \"text\"")
expect (src).to_contain("fn _gui_handle_text")
expect (src).to_contain("clipboard-copy")
expect (src).to_contain("clipboard-paste")
```

</details>

#### gui shell handles SDL focus events

- gui shell handles SDL focus events


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gui shell handles SDL focus events")
val src = file_read_text("src/app/editor/gui_shell.spl") ?? ""
expect (src).to_contain("elif event_kind == \"focus\"")
expect (src).to_contain("elif event_kind == \"blur\"")
```

</details>

#### main exposes --gui-sdl mode

- main exposes --gui-sdl mode


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("main exposes --gui-sdl mode")
val src = file_read_text("src/app/editor/main.spl") ?? ""
expect (src).to_contain("\"--gui-sdl\"")
expect (src).to_contain("gui_shell_run_sdl(session)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_gui_sdl_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Editor GUI SDL Bridge.
- Editor GUI SDL Bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `2c05ff8e6ba7e3f61f5ca864fef30df84afe929a19266374f0295e19f92f11d2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2c05ff8e6ba7e3f61f5ca864fef30df84afe929a19266374f0295e19f92f11d2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2c05ff8e6ba7e3f61f5ca864fef30df84afe929a19266374f0295e19f92f11d2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/editor_gui_sdl_spec.spl
mirror: doc/06_spec/03_system/gui/editor_gui_sdl_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_gui_sdl_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_gui_sdl_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_gui_sdl_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gui_sdl_bridge.spl exists and is non-empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_gui_sdl_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gui_sdl_init function declared' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_gui_sdl_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gui_sdl_render_text_block function declared' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
