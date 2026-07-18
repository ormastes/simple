# Chat Tui Specification

> <details>

<!-- sdn-diagram:id=chat_tui_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chat_tui_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chat_tui_spec -> app
chat_tui_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chat_tui_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chat Tui Specification

## Scenarios

### TUI pure formatting

#### labels user and assistant turns distinctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tui_role_label("user")).to_equal("You")
expect(tui_role_label("assistant")).to_equal("Claude")
```

</details>

#### formats a turn line with its role label

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_turn_line("user", "hello")).to_equal("You: hello")
expect(format_turn_line("assistant", "hi")).to_equal("Claude: hi")
```

</details>

#### styles user vs assistant turns differently

- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val us = tui_role_style("user")
val asst = tui_role_style("assistant")
expect(us.fg).to_equal(COLOR_CYAN)
expect(asst.fg).to_equal(COLOR_GREEN)
assert_true(us.fg != asst.fg)
```

</details>

#### formats a tool-call line

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_tool_line("bash", "ok", "output")).to_equal("  -> tool bash [ok]: output")
```

</details>

#### styles error tool lines red and ok tool lines yellow

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(tui_tool_style("error").fg).to_equal(COLOR_RED)
expect(tui_tool_style("ok").fg).to_equal(COLOR_YELLOW)
```

</details>

### Renderer-seam selection

#### explicit plain flag forces plain even on a tty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(select_renderer_mode("plain", true)).to_equal("plain")
```

</details>

#### explicit tui flag forces tui even without a tty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(select_renderer_mode("tui", false)).to_equal("tui")
```

</details>

#### auto picks tui on a tty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(select_renderer_mode("auto", true)).to_equal("tui")
```

</details>

#### auto falls back to plain when not a tty

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(select_renderer_mode("auto", false)).to_equal("plain")
```

</details>

### Transcript rendering

#### appends a styled user turn to the transcript

- tui transcript reset
- render turn
   - Expected: tui_transcript_len() equals `1`
   - Expected: tui_transcript_line_text(0) equals `You: hi there`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
tui_transcript_reset()
render_turn("user", "hi there")
expect(tui_transcript_len()).to_equal(1)
expect(tui_transcript_line_text(0)).to_equal("You: hi there")
```

</details>

#### appends a styled tool-call line to the transcript

- tui transcript reset
- render tool call
   - Expected: tui_transcript_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
tui_transcript_reset()
render_tool_call("bash", "ok", "42")
expect(tui_transcript_len()).to_equal(1)
expect(tui_transcript_line_text(0)).to_contain("tool bash [ok]")
```

</details>

### Agent-loop renderer seam

#### routes tool calls through render_tool_call in TUI mode

- tui transcript reset
   - Expected: result.tool_calls_made equals `1`
   - Expected: tui_transcript_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
tui_transcript_reset()
val p = default_policy(WS_ROOT)
val result = run_agent_loop_rendered(p, [new_user_message("go")], _one_tool, 25, tui_tool_renderer)
expect(result.tool_calls_made).to_equal(1)
expect(tui_transcript_len()).to_equal(1)
expect(tui_transcript_line_text(0)).to_contain("tool bash")
expect(tui_transcript_line_text(0)).to_contain("[error]")
```

</details>

#### leaves the TUI transcript untouched on the plain print path

- tui transcript reset
   - Expected: result.tool_calls_made equals `1`
   - Expected: tui_transcript_len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
tui_transcript_reset()
val p = default_policy(WS_ROOT)
val result = run_agent_loop(p, [new_user_message("go")], _one_tool, 25)
expect(result.tool_calls_made).to_equal(1)
expect(tui_transcript_len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/chat_tui_spec.spl` |
| Updated | 2026-07-07 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TUI pure formatting
- Renderer-seam selection
- Transcript rendering
- Agent-loop renderer seam

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
