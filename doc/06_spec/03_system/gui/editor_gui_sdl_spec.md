# Editor Gui Sdl Specification

> 1. expect

<!-- sdn-diagram:id=editor_gui_sdl_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_gui_sdl_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_gui_sdl_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_gui_sdl_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Gui Sdl Specification

## Scenarios

### Editor GUI SDL Bridge

#### gui_sdl_bridge.spl exists and is non-empty

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).contains("gui_sdl_bridge")
```

</details>

#### gui_sdl_init function declared

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).contains("fn gui_sdl_init(")
```

</details>

#### gui_sdl_render_text_block function declared

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).contains("fn gui_sdl_render_text_block(")
```

</details>

#### gui_sdl_present_frame function declared

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).contains("fn gui_sdl_present_frame(")
```

</details>

#### gui_sdl_poll function declared

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).contains("fn gui_sdl_poll(")
```

</details>

#### gui_sdl_poll maps printable key symbols to text

1. expect
2. expect
3. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).contains("char_from_code(sym)")
expect (src).contains("data: \"Enter\"")
expect (src).contains("data: \"Backspace\"")
```

</details>

#### gui_sdl_poll maps modifier key chords

1. expect
2. expect
3. expect
4. expect
5. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).contains("rt_sdl_event_key_mod()")
expect (src).contains("\"Ctrl+\" + letter")
expect (src).contains("\"Ctrl+Shift+\" + letter")
expect (src).contains("Shift+Alt+Right")
expect (src).contains("Shift+Alt+Left")
```

</details>

#### gui_sdl_poll maps text input events

1. expect
2. expect
3. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).contains("extern fn rt_sdl_event_text() -> text")
expect (src).contains("if ev == 9:")
expect (src).contains("GuiEvent(kind: \"text\", data: rt_sdl_event_text())")
```

</details>

#### gui_sdl_poll maps window resize and focus events

1. expect
2. expect
3. expect
4. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).contains("rt_sdl_event_window_event_id()")
expect (src).contains("GuiEvent(kind: \"resize\"")
expect (src).contains("GuiEvent(kind: \"focus\"")
expect (src).contains("GuiEvent(kind: \"blur\"")
```

</details>

#### rt_sdl_create_window extern declared

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).contains("extern fn rt_sdl_create_window(")
```

</details>

#### rt_sdl_present_rgba extern declared

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).contains("extern fn rt_sdl_present_rgba(")
```

</details>

#### rt_sdl_poll_event extern declared

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/editor/70.backend/gui_sdl_bridge.spl") ?? ""
expect (src).contains("extern fn rt_sdl_poll_event(")
```

</details>

#### gui_shell_present_frame_sdl added to gui_shell.spl

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/app/editor/gui_shell.spl") ?? ""
expect (src).contains("fn gui_shell_present_frame_sdl(")
```

</details>

#### gui_shell_present_frame_sdl delegates to gui_sdl_present_frame

1. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/app/editor/gui_shell.spl") ?? ""
expect (src).contains("gui_sdl_present_frame(window, frame)")
```

</details>

<details>
<summary>Advanced: gui shell has SDL run loop with runtime event polling</summary>

#### gui shell has SDL run loop with runtime event polling

1. expect
2. expect
3. expect
4. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/app/editor/gui_shell.spl") ?? ""
expect (src).contains("fn gui_shell_run_sdl(session: EditSession)")
expect (src).contains("gui_sdl_init(state.config.window_title")
expect (src).contains("gui_shell_poll_event_sdl()")
expect (src).contains("gui_sdl_shutdown(window)")
```

</details>


</details>

#### gui shell routes SDL text and clipboard shortcuts

1. expect
2. expect
3. expect
4. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/app/editor/gui_shell.spl") ?? ""
expect (src).contains("elif event_kind == \"text\"")
expect (src).contains("fn _gui_handle_text")
expect (src).contains("clipboard-copy")
expect (src).contains("clipboard-paste")
```

</details>

#### gui shell handles SDL focus events

1. expect
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/app/editor/gui_shell.spl") ?? ""
expect (src).contains("elif event_kind == \"focus\"")
expect (src).contains("elif event_kind == \"blur\"")
```

</details>

#### main exposes --gui-sdl mode

1. expect
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/app/editor/main.spl") ?? ""
expect (src).contains("\"--gui-sdl\"")
expect (src).contains("gui_shell_run_sdl(session)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_gui_sdl_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Editor GUI SDL Bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
