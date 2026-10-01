# LLM Caret Chat TUI Unit Spec

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should label user and assistant turns distinctly
- Verify: should label user and assistant turns distinctly
   - Expected: tui_role_label("user") equals `You`
   - Expected: tui_role_label("assistant") equals `Assistant`

## should label user and assistant turns distinctly

**Group:** TUI pure formatting

<details>
<summary>Executable SSpec</summary>

```simple
expect(tui_role_label("user")).to_equal("You")
expect(tui_role_label("assistant")).to_equal("Claude")
```

</details>

## should format a turn line with its role label

**Group:** TUI pure formatting

<details>
<summary>Executable SSpec</summary>

```simple
expect(format_turn_line("user", "hello")).to_equal("You: hello")
expect(format_turn_line("assistant", "hi")).to_equal("Claude: hi")
```

</details>

## should style user vs assistant turns differently

**Group:** TUI pure formatting

<details>
<summary>Executable SSpec</summary>

```simple
# @req REQ-SSPEC-UNIT
step("should format a turn line with its role label")
step("Verify: should format a turn line with its role label")
expect(format_turn_line("user", "hello")).to_equal("You: hello")
expect(format_turn_line("assistant", "hi")).to_equal("Claude: hi")
```

</details>

#### styles user vs assistant turns differently

- assert true

**Group:** TUI pure formatting

<details>
<summary>Executable SSpec</summary>

```simple
expect(format_turn_line("user", "hello")).to_equal("You: hello")
expect(format_turn_line("assistant", "hi")).to_equal("Claude: hi")
```

</details>

## should style user vs assistant turns differently

**Group:** TUI pure formatting

<details>
<summary>Executable SSpec</summary>

```simple
val us = tui_role_style("user")
val asst = tui_role_style("assistant")
expect(us.fg).to_equal(COLOR_CYAN)
expect(asst.fg).to_equal(COLOR_GREEN)
assert_true(us.fg != asst.fg)
```

</details>

## should format a tool-call line

**Group:** TUI pure formatting

<details>
<summary>Executable SSpec</summary>

```simple
expect(format_tool_line("bash", "ok", "output")).to_equal("  -> tool bash [ok]: output")
```

</details>

## should style error tool lines red and ok tool lines yellow

**Group:** TUI pure formatting

<details>
<summary>Executable SSpec</summary>

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

## should explicit plain flag forces plain even on a tty

**Group:** Renderer-seam selection

<details>
<summary>Executable SSpec</summary>

```simple
expect(select_renderer_mode("plain", true)).to_equal("plain")
```

</details>

## should explicit tui flag forces tui even without a tty

**Group:** Renderer-seam selection

<details>
<summary>Executable SSpec</summary>

```simple
expect(select_renderer_mode("tui", false)).to_equal("tui")
```

</details>

## should auto picks tui on a tty

**Group:** Renderer-seam selection

<details>
<summary>Executable SSpec</summary>

```simple
expect(select_renderer_mode("auto", true)).to_equal("tui")
```

</details>

## should auto falls back to plain when not a tty

**Group:** Renderer-seam selection

<details>
<summary>Executable SSpec</summary>

```simple
expect(select_renderer_mode("auto", false)).to_equal("plain")
```

</details>

## should classify dumb and interactive TERM values

**Group:** Renderer-seam selection

<details>
<summary>Executable SSpec</summary>

```simple
# @req REQ-SSPEC-UNIT
step("should classify dumb and interactive TERM values")
step("Verify: should classify dumb and interactive TERM values")
expect(caret_term_supports_tui(nil)).to_be(false)
expect(caret_term_supports_tui("")).to_be(false)
expect(caret_term_supports_tui("dumb")).to_be(false)
expect(caret_term_supports_tui("xterm-256color")).to_be(true)
```

</details>

### Transcript rendering

#### appends a styled user turn to the transcript

- tui transcript reset
- render turn
   - Expected: tui_transcript_len() equals `1`
   - Expected: tui_transcript_line_text(0) equals `You: hi there`

**Group:** Transcript rendering

<details>
<summary>Executable SSpec</summary>

```simple
tui_transcript_reset()
render_turn("user", "hi there")
expect(tui_transcript_len()).to_equal(1)
expect(tui_transcript_line_text(0)).to_equal("You: hi there")
```

</details>

## should append a styled tool-call line to the transcript

**Group:** Transcript rendering

<details>
<summary>Executable SSpec</summary>

```simple
tui_transcript_reset()
render_tool_call("bash", "ok", "42")
expect(tui_transcript_len()).to_equal(1)
expect(tui_transcript_line_text(0)).to_contain("tool bash [ok]")
```

</details>

## should route tool calls through render_tool_call in TUI mode

**Group:** Agent-loop renderer seam

<details>
<summary>Executable SSpec</summary>

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

## should leave the TUI transcript untouched on the plain print path

**Group:** Agent-loop renderer seam

<details>
<summary>Executable SSpec</summary>

```simple
tui_transcript_reset()
val p = default_policy(WS_ROOT)
val result = run_agent_loop(p, [new_user_message("go")], _one_tool, 25)
expect(result.tool_calls_made).to_equal(1)
expect(tui_transcript_len()).to_equal(0)
```

</details>

## should thread tool_result turns back into final_transcript (M2 fix)

**Group:** Agent-loop renderer seam

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should thread tool_result turns back into final_transcript (M2 fix)")
step("Verify: should thread tool_result turns back into final_transcript (M2 fix)")
val p = default_policy(WS_ROOT)
val result = run_agent_loop(p, [new_user_message("go")], _one_tool, 25)
# initial user turn + tool_result turn + final assistant turn = 3.
# Before the fix, callers only had `initial + [final_text]` (len 2)
# and the tool_result turn was silently dropped between top-level
# calls - this is the exact gap the guide's M2 milestone flagged.
expect(result.final_transcript.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(result.final_transcript[1].content).to_contain("tool_result")
```

</details>

### Markdown-lite rendering

#### should render a plain single-line turn exactly as format_turn_line would

- should render a plain single-line turn exactly as format_turn_line would
- Verify: should render a plain single-line turn exactly as format_turn_line would
   - Expected: tui_transcript_len() equals `1`
   - Expected: tui_transcript_line_text(0) equals `Assistant: hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should render a plain single-line turn exactly as format_turn_line would")
step("Verify: should render a plain single-line turn exactly as format_turn_line would")
tui_transcript_reset()
render_turn("assistant", "hi")
expect(tui_transcript_len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(tui_transcript_line_text(0)).to_equal("Assistant: hi")
```

</details>

#### should split multi-line content into one transcript line per source line

- should split multi-line content into one transcript line per source line
- Verify: should split multi-line content into one transcript line per source line
   - Expected: tui_transcript_len() equals `2`
   - Expected: tui_transcript_line_text(0) equals `Assistant: line one`
   - Expected: tui_transcript_line_text(1) equals `line two`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should split multi-line content into one transcript line per source line")
step("Verify: should split multi-line content into one transcript line per source line")
tui_transcript_reset()
render_turn("assistant", "line one\nline two")
expect(tui_transcript_len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(tui_transcript_line_text(0)).to_equal("Assistant: line one")
expect(tui_transcript_line_text(1)).to_equal("line two")
```

</details>

#### should detect fenced code block markers

- should detect fenced code block markers
- Verify: should detect fenced code block markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should detect fenced code block markers")
step("Verify: should detect fenced code block markers")
expect(is_fence_line("```")).to_be(true)
expect(is_fence_line("```python")).to_be(true)
expect(is_fence_line("plain text")).to_be(false)
```

</details>

#### should indent bullet lines and leave others untouched

- should indent bullet lines and leave others untouched
- Verify: should indent bullet lines and leave others untouched
   - Expected: bullet_indent("- item") equals `  - item`
   - Expected: bullet_indent("* item") equals `  * item`
   - Expected: bullet_indent("plain") equals `plain`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should indent bullet lines and leave others untouched")
step("Verify: should indent bullet lines and leave others untouched")
expect(bullet_indent("- item")).to_equal("  - item")
expect(bullet_indent("* item")).to_equal("  * item")
expect(bullet_indent("plain")).to_equal("plain")
```

</details>

#### should render a fenced code block dim with indentation preserved

- should render a fenced code block dim with indentation preserved
- Verify: should render a fenced code block dim with indentation preserved
   - Expected: tui_transcript_len() equals `3`
   - Expected: tui_transcript_line_text(1) equals `  indented code`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should render a fenced code block dim with indentation preserved")
step("Verify: should render a fenced code block dim with indentation preserved")
tui_transcript_reset()
render_turn("assistant", "```\n  indented code\n```")
expect(tui_transcript_len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(tui_transcript_line_text(1)).to_equal("  indented code")
```

</details>

#### should split inline code spans into separate segments

- should split inline code spans into separate segments
- Verify: should split inline code spans into separate segments
   - Expected: segs.len() equals `3`
   - Expected: segs[0].content equals `run `
   - Expected: segs[1].content equals `cmd`
   - Expected: segs[2].content equals ` now`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should split inline code spans into separate segments")
step("Verify: should split inline code spans into separate segments")
val segs = inline_code_segments("run `cmd` now", tui_default_style())
expect(segs.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(segs[0].content).to_equal("run ")
expect(segs[1].content).to_equal("cmd")
expect(segs[2].content).to_equal(" now")
```

</details>

#### should markdown_turn_lines prefixes only the first line with the role label

- should markdown_turn_lines prefixes only the first line with the role label
- Verify: should markdown_turn_lines prefixes only the first line with the role label
   - Expected: lines.len() equals `2`
   - Expected: lines[0].segments[0].content equals `You: a`
   - Expected: lines[1].segments[0].content equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should markdown_turn_lines prefixes only the first line with the role label")
step("Verify: should markdown_turn_lines prefixes only the first line with the role label")
val lines = markdown_turn_lines("user", "a\nb")
expect(lines.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(lines[0].segments[0].content).to_equal("You: a")
expect(lines[1].segments[0].content).to_equal("b")
```

</details>

### Scrollback window (visible_window)

#### should auto-follow (-1) shows the tail when content exceeds the viewport

- should auto-follow (-1) shows the tail when content exceeds the viewport
- Verify: should auto-follow (-1) shows the tail when content exceeds the viewport
   - Expected: start equals `6`
   - Expected: end equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should auto-follow (-1) shows the tail when content exceeds the viewport")
step("Verify: should auto-follow (-1) shows the tail when content exceeds the viewport")
val (start, end) = visible_window(10, 4, -1)
expect(start).to_equal(6)  # oracle: 6 — named expected value from the requirement
expect(end).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>

#### should auto-follow shows everything when content fits the viewport

- should auto-follow shows everything when content fits the viewport
- Verify: should auto-follow shows everything when content fits the viewport
   - Expected: start equals `0`
   - Expected: end equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should auto-follow shows everything when content fits the viewport")
step("Verify: should auto-follow shows everything when content fits the viewport")
val (start, end) = visible_window(3, 4, -1)
expect(start).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(end).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>

#### should a fixed scroll_top clamps to the valid range

- should a fixed scroll_top clamps to the valid range
- Verify: should a fixed scroll_top clamps to the valid range
   - Expected: start equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should a fixed scroll_top clamps to the valid range")
step("Verify: should a fixed scroll_top clamps to the valid range")
val (start, end) = visible_window(10, 4, 100)
expect(start).to_equal(6)  # oracle: 6 — named expected value from the requirement
```

</details>

#### should a fixed scroll_top of 0 shows the very top

- should a fixed scroll_top of 0 shows the very top
- Verify: should a fixed scroll_top of 0 shows the very top
   - Expected: start equals `0`
   - Expected: end equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should a fixed scroll_top of 0 shows the very top")
step("Verify: should a fixed scroll_top of 0 shows the very top")
val (start, end) = visible_window(10, 4, 0)
expect(start).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(end).to_equal(4)  # oracle: 4 — named expected value from the requirement
```

</details>

### Scroll paging (Ctrl-P/Ctrl-N)

#### should be not scrolled by default

- should be not scrolled by default
- Verify: should be not scrolled by default


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should be not scrolled by default")
step("Verify: should be not scrolled by default")
tui_transcript_reset()
expect(is_scrolled()).to_be(false)
```

</details>

#### should page up away from auto-follow, and resume after enough pages down

- should page up away from auto-follow, and resume after enough pages down
- Verify: should page up away from auto-follow, and resume after enough pages down


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should page up away from auto-follow, and resume after enough pages down")
step("Verify: should page up away from auto-follow, and resume after enough pages down")
tui_transcript_reset()
var i = 0
while i < 20:
    render_turn("user", "line " + i.to_text())
    i = i + 1
val len = tui_transcript_len()
scroll_page_up(len, 5)
scroll_page_up(len, 5)
scroll_page_up(len, 5)
expect(is_scrolled()).to_be(true)
scroll_page_down(len, 5)
scroll_page_down(len, 5)
scroll_page_down(len, 5)
expect(is_scrolled()).to_be(false)
```

</details>

### TUI frame component state

#### should expose tail and fixed scrollback content

- should expose tail and fixed scrollback content
- Render four production transcript lines
   - Expected: tail.len() equals `2`
   - Expected: tail[0].segments[0].content equals `You: two`
   - Expected: tail[1].segments[0].content equals `You: three`
- Page up and read the fixed production viewport
   - Expected: fixed[0].segments[0].content equals `You: zero`
   - Expected: fixed[1].segments[0].content equals `You: one`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should expose tail and fixed scrollback content")
step("Render four production transcript lines")
tui_transcript_reset()
for content in ["zero", "one", "two", "three"]:
    render_turn("user", content)
val tail = _visible_content(2)
expect(tail.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(tail[0].segments[0].content).to_equal("You: two")
expect(tail[1].segments[0].content).to_equal("You: three")
step("Page up and read the fixed production viewport")
scroll_page_up(tui_transcript_len(), 2)
val fixed = _visible_content(2)
expect(fixed[0].segments[0].content).to_equal("You: zero")
expect(fixed[1].segments[0].content).to_equal("You: one")
```

</details>

#### should compose status with turn and waiting state

- should compose status with turn and waiting state
- Format status through the production component helper
   - Expected: _status_line(ui, 7, false) equals `provider=claude  turn 7`
   - Expected: _status_line(make_chat_tui("Caret"), 0, false) equals `turn 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should compose status with turn and waiting state")
step("Format status through the production component helper")
val ui = make_chat_tui_with_status("Caret", "provider=claude")
expect(_status_line(ui, 7, false)).to_equal("provider=claude  turn 7")
expect(_status_line(ui, 8, true)).to_equal(
    "provider=claude  turn 8  (waiting for response...)"
)
expect(_status_line(make_chat_tui("Caret"), 0, false)).to_equal("turn 0")
```

</details>

#### should add the follow hint only while scrolled

- should add the follow hint only while scrolled
- Compare follow and scrolled production hints
   - Expected: _hint_line(ui) equals `ui.hint`
   - Expected: _hint_line(ui) equals `ui.hint + " [scrolled - Ctrl-N to follow]"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should add the follow hint only while scrolled")
step("Compare follow and scrolled production hints")
tui_transcript_reset()
val ui = make_chat_tui("Caret")
expect(_hint_line(ui)).to_equal(ui.hint)
for content in ["zero", "one", "two"]:
    render_turn("assistant", content)
scroll_page_up(tui_transcript_len(), 1)
expect(_hint_line(ui)).to_equal(ui.hint + " [scrolled - Ctrl-N to follow]")
```

</details>

### Slash command parsing

#### should recognize lines starting with /

- should recognize lines starting with /
- Verify: should recognize lines starting with /


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should recognize lines starting with /")
step("Verify: should recognize lines starting with /")
expect(is_slash_command("/help")).to_be(true)
expect(is_slash_command("hello")).to_be(false)
```

</details>

#### should split a command and its argument

- should split a command and its argument
- Verify: should split a command and its argument
   - Expected: cmd equals `model`
   - Expected: arg equals `gpt-4o`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should split a command and its argument")
step("Verify: should split a command and its argument")
val (cmd, arg) = parse_slash_command("/model gpt-4o")
expect(cmd).to_equal("model")
expect(arg).to_equal("gpt-4o")
```

</details>

#### should split a command with no argument

- should split a command with no argument
- Verify: should split a command with no argument
   - Expected: cmd equals `help`
   - Expected: arg equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should split a command with no argument")
step("Verify: should split a command with no argument")
val (cmd, arg) = parse_slash_command("/help")
expect(cmd).to_equal("help")
expect(arg).to_equal("")
```

</details>

### Slash command dispatch

#### should /help returns the help text

- should /help returns the help text
- Verify: should /help returns the help text


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should /help returns the help text")
step("Verify: should /help returns the help text")
val r = dispatch_slash("help", "", _test_hooks())
expect(r.message).to_contain("/model <name>")
expect(r.message.contains("/debug-tool-call")).to_be(false)
expect(r.message.contains("/debug_tool_call")).to_be(false)
expect(r.message.contains("/remote-setup")).to_be(false)
expect(r.message.contains("/remote_setup")).to_be(false)
```

</details>

#### should /exit sets exit=true

- should /exit sets exit=true
- Verify: should /exit sets exit=true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should /exit sets exit=true")
step("Verify: should /exit sets exit=true")
val r = dispatch_slash("exit", "", _test_hooks())
expect(r.exit).to_be(true)
```

</details>

#### should /quit is an alias for /exit

- should /quit is an alias for /exit
- Verify: should /quit is an alias for /exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should /quit is an alias for /exit")
step("Verify: should /quit is an alias for /exit")
val r = dispatch_slash("quit", "", _test_hooks())
expect(r.exit).to_be(true)
```

</details>

#### should /new clears the conversation

- should /new clears the conversation
- Verify: should /new clears the conversation
   - Expected: r.new_session_id equals `s-new`
   - Expected: r.status_session equals `s-new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should /new clears the conversation")
step("Verify: should /new clears the conversation")
val r = dispatch_slash("new", "", _test_hooks())
expect(r.new_conv).to_be(true)
expect(r.new_session_id).to_equal("s-new")
expect(r.status_session).to_equal("s-new")
```

</details>

#### should apply a new conversation session to visible TUI status

- should apply a new conversation session to visible TUI status
- Verify: should apply a new conversation session to visible TUI status


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should apply a new conversation session to visible TUI status")
step("Verify: should apply a new conversation session to visible TUI status")
val ui = make_chat_tui_with_status(
    "llm_caret - dummy",
    "provider=dummy model=dummy-hello session=s0"
)
val result = dispatch_slash("new", "", _test_hooks())
val new_ui = apply_slash_status(ui, result)
expect(new_ui.status).to_equal(
    "provider=dummy model=dummy-hello session=s-new"
)
```

</details>

#### should /model with no argument is a usage error

- should /model with no argument is a usage error
- Verify: should /model with no argument is a usage error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should /model with no argument is a usage error")
step("Verify: should /model with no argument is a usage error")
val r = dispatch_slash("model", "", _test_hooks())
expect(r.message).to_contain("Usage")
```

</details>

#### should /model <name> calls hooks.on_model

- should /model <name> calls hooks.on_model
- Verify: should /model <name> calls hooks.on_model
   - Expected: r.message equals `model set to gpt-4o`
   - Expected: r.status_model equals `gpt-4o`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should /model <name> calls hooks.on_model")
step("Verify: should /model <name> calls hooks.on_model")
val r = dispatch_slash("model", "gpt-4o", _test_hooks())
expect(r.message).to_equal("model set to gpt-4o")
expect(r.status_model).to_equal("gpt-4o")
```

</details>

#### should /provider <name> calls hooks.on_provider

- should /provider <name> calls hooks.on_provider
- Verify: should /provider <name> calls hooks.on_provider
   - Expected: r.message equals `provider set to openai`
   - Expected: r.status_provider equals `openai`
   - Expected: r.status_model equals `gpt-4o`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should /provider <name> calls hooks.on_provider")
step("Verify: should /provider <name> calls hooks.on_provider")
val r = dispatch_slash("provider", "openai", _test_hooks())
expect(r.message).to_equal("provider set to openai")
expect(r.status_provider).to_equal("openai")
expect(r.status_model).to_equal("gpt-4o")
```

</details>

#### should not refresh visible status after a rejected provider

- should not refresh visible status after a rejected provider
- Verify: should not refresh visible status after a rejected provider
   - Expected: result.message equals `unknown provider: missing`
   - Expected: result.status_provider equals ``
   - Expected: unchanged.status equals `ui.status`
   - Expected: unchanged.title equals `ui.title`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should not refresh visible status after a rejected provider")
step("Verify: should not refresh visible status after a rejected provider")
val ui = make_chat_tui_with_status(
    "llm_caret - dummy",
    "provider=dummy model=dummy-hello session=s0"
)
val result = dispatch_slash(
    "provider", "missing", _test_hooks_provider_reject()
)
val unchanged = apply_slash_status(ui, result)
expect(result.message).to_equal("unknown provider: missing")
expect(result.status_provider).to_equal("")
expect(unchanged.status).to_equal(ui.status)
expect(unchanged.title).to_equal(ui.title)
```

</details>

#### should apply provider and model changes to visible TUI status

- should apply provider and model changes to visible TUI status
- Verify: should apply provider and model changes to visible TUI status
   - Expected: provider_ui.title equals `llm_caret - openai`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should apply provider and model changes to visible TUI status")
step("Verify: should apply provider and model changes to visible TUI status")
val ui = make_chat_tui_with_status(
    "llm_caret - dummy",
    "provider=dummy model=dummy-hello session=s0"
)
val provider_result = dispatch_slash(
    "provider", "openai", _test_hooks()
)
val provider_ui = apply_slash_status(ui, provider_result)
expect(provider_ui.title).to_equal("llm_caret - openai")
expect(provider_ui.status).to_equal(
    "provider=openai model=gpt-4o session=s0"
)

val model_result = dispatch_slash(
    "model", "gpt-4o", _test_hooks()
)
val model_ui = apply_slash_status(provider_ui, model_result)
expect(model_ui.status).to_equal(
    "provider=openai model=gpt-4o session=s0"
)
```

</details>

#### should /sessions calls hooks.on_sessions

- should /sessions calls hooks.on_sessions
- Verify: should /sessions calls hooks.on_sessions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should /sessions calls hooks.on_sessions")
step("Verify: should /sessions calls hooks.on_sessions")
val r = dispatch_slash("sessions", "", _test_hooks())
expect(r.message).to_contain("s1")
```

</details>

#### should /resume <id> found: replaces the conversation

- should /resume <id> found: replaces the conversation
- Verify: should /resume <id> found: replaces the conversation
   - Expected: r.new_session_id equals `abc`
   - Expected: r.status_session equals `abc`
   - Expected: r.status_provider equals `claude_cli`
   - Expected: r.status_model equals `sonnet`
   - Expected: r.loaded_messages.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should /resume <id> found: replaces the conversation")
step("Verify: should /resume <id> found: replaces the conversation")
val r = dispatch_slash("resume", "abc", _test_hooks())
expect(r.replace_conv).to_be(true)
expect(r.new_session_id).to_equal("abc")
expect(r.status_session).to_equal("abc")
expect(r.status_provider).to_equal("claude_cli")
expect(r.status_model).to_equal("sonnet")
expect(r.loaded_messages.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### should apply a resumed session to visible TUI status

- should apply a resumed session to visible TUI status
- Verify: should apply a resumed session to visible TUI status
   - Expected: resumed_ui.title equals `llm_caret - claude_cli`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should apply a resumed session to visible TUI status")
step("Verify: should apply a resumed session to visible TUI status")
val ui = make_chat_tui_with_status(
    "llm_caret - dummy",
    "provider=dummy model=dummy-hello session=s0"
)
val result = dispatch_slash("resume", "abc", _test_hooks())
val resumed_ui = apply_slash_status(ui, result)
expect(resumed_ui.title).to_equal("llm_caret - claude_cli")
expect(resumed_ui.status).to_equal(
    "provider=claude_cli model=sonnet session=abc"
)
```

</details>

#### should /resume <id> not found: reports it, does not replace

- should /resume <id> not found: reports it, does not replace
- Verify: should /resume <id> not found: reports it, does not replace
   - Expected: r.status_session equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should /resume <id> not found: reports it, does not replace")
step("Verify: should /resume <id> not found: reports it, does not replace")
val r = dispatch_slash("resume", "missing-id", _test_hooks_missing())
expect(r.replace_conv).to_be(false)
expect(r.message).to_contain("no saved session")
expect(r.status_session).to_equal("")
```

</details>

#### should report unknown /commands are reported, never silently sent to the model

- should report unknown /commands are reported, never silently sent to the model
- Verify: should report unknown /commands are reported, never silently sent to the model


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should report unknown /commands are reported, never silently sent to the model")
step("Verify: should report unknown /commands are reported, never silently sent to the model")
val r = dispatch_slash("bogus", "", _test_hooks())
expect(r.message).to_contain("Unknown command")
expect(r.exit).to_be(false)
expect(r.new_conv).to_be(false)
expect(r.replace_conv).to_be(false)
```

</details>

#### should reject hidden commands by default and execute an enabled fixture

- should reject hidden commands by default and execute an enabled fixture
- Verify: should reject hidden commands by default and execute an enabled fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject hidden commands by default and execute an enabled fixture")
step("Verify: should reject hidden commands by default and execute an enabled fixture")
val rejected = dispatch_slash(
    "debug-tool-call", "call-1", _test_hooks()
)
# Reproduce (2026-08-25): the old oracle compared the reject message
# against a *different* command name and could never hold — observed
# `Unknown command: /debug-tool-call (try /help)` vs
# `Unknown command: /not-registered (try /help)`. The non-disclosure
# property is that a gated hidden name renders exactly like an unknown
# command of the SAME name (chat_tui_runtime_spec pins the same form).
val unknown = dispatch_slash("not-registered", "", _test_hooks())
expect(rejected.message).to_equal(
    "Unknown command: /debug-tool-call (try /help)"
)
expect(unknown.message).to_equal(
    "Unknown command: /not-registered (try /help)"
)
expect(rejected.message.replace("debug-tool-call", "not-registered")).to_equal(
    unknown.message
)
val admitted = dispatch_slash(
    "debug-tool-call", "call-1", _test_hooks_hidden()
)
expect(admitted.message).to_equal(
    "hidden command executed: debug-tool-call call-1"
)
```

</details>

#### should reject disabled registry commands under every fixture

- should reject disabled registry commands under every fixture
- Verify: should reject disabled registry commands under every fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should reject disabled registry commands under every fixture")
step("Verify: should reject disabled registry commands under every fixture")
val result = dispatch_slash(
    "remote-setup", "", _test_hooks_hidden()
)
expect(result.message).to_contain("Command disabled")
```

</details>

#### should support help and conversation-reset aliases

- should support help and conversation-reset aliases
- Verify: should support help and conversation-reset aliases


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should support help and conversation-reset aliases")
step("Verify: should support help and conversation-reset aliases")
expect(dispatch_slash("?", "", _test_hooks()).message).to_equal(
    slash_help_text()
)
expect(dispatch_slash("clear", "", _test_hooks()).new_conv).to_be(true)
expect(dispatch_slash("reset", "", _test_hooks()).new_conv).to_be(true)
```

</details>

#### should distinguish recognized registry commands from unknown input

- should distinguish recognized registry commands from unknown input
- Verify: should distinguish recognized registry commands from unknown input


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should distinguish recognized registry commands from unknown input")
step("Verify: should distinguish recognized registry commands from unknown input")
val known = dispatch_slash("config", "", _test_hooks())
val unknown = dispatch_slash("not-registered", "", _test_hooks())
expect(known.message).to_contain("not implemented in Caret")
expect(known.message).to_contain("/config")
expect(known.message == unknown.message).to_be(false)
```

</details>

#### should enforce registry gates and canonical handlers through aliases

- should enforce registry gates and canonical handlers through aliases
- Verify: should enforce registry gates and canonical handlers through aliases


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should enforce registry gates and canonical handlers through aliases")
step("Verify: should enforce registry gates and canonical handlers through aliases")
val hidden = dispatch_slash(
    "debug_tool_call", "payload", _test_hooks()
)
# Similar case to the canonical-name reject above: the alias form must
# also render as an unknown command of the same (alias) name.
val unknown = dispatch_slash(
    "not-registered", "payload", _test_hooks()
)
expect(hidden.message).to_equal(
    "Unknown command: /debug_tool_call (try /help)"
)
expect(hidden.message.replace("debug_tool_call", "not-registered")).to_equal(
    unknown.message
)

val admitted = dispatch_slash(
    "debug_tool_call", "payload", _test_hooks_hidden()
)
expect(admitted.message).to_equal(
    "hidden command executed: debug-tool-call payload"
)
expect(dispatch_slash(
    "settings", "", _test_hooks()
).message).to_contain("/config")
expect(dispatch_slash(
    "remote_setup", "", _test_hooks_hidden()
).message).to_contain("Command disabled")
```

</details>

#### should canonicalize accepted promptless commands without state mutation

- should canonicalize accepted promptless commands without state mutation
- Load the accepted promptless command aliases
- Dispatch the command through the shipped Caret path
- Check canonical output and zero model submission
   - Expected: cases.len() equals `4`
   - Expected: SUBMISSION_RESPONDER_CALLS equals `0`
   - Expected: SUBMISSION_PERSIST_CALLS equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should canonicalize accepted promptless commands without state mutation")
step("Load the accepted promptless command aliases")
val cases = setup_promptless_command_cases()
_reset_submission_call_counts()
step("Dispatch the command through the shipped Caret path")
for case in cases:
    check_promptless_dispatch(case)
step("Check canonical output and zero model submission")
expect(cases.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(SUBMISSION_RESPONDER_CALLS).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(SUBMISSION_PERSIST_CALLS).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

### TUI submission state transition

#### should stop on the quit alias without mutating conversation state

- should stop on the quit alias without mutating conversation state
- Verify: should stop on the quit alias without mutating conversation state
   - Expected: result.session_id equals `s0`
   - Expected: result.conversation.len() equals `1`
   - Expected: result.conversation[0].content equals `keep this`
   - Expected: tui_transcript_len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should stop on the quit alias without mutating conversation state")
step("Verify: should stop on the quit alias without mutating conversation state")
tui_transcript_reset()
val result = run_chat_tui_submission(
    make_chat_tui("llm_caret"),
    [new_user_message("keep this")], "s0", "  /quit  ",
    default_policy("build/tmp/caret-tui-unit"),
    _submission_response, _test_hooks()
)
expect(result.running).to_be(false)
expect(result.submitted_to_model).to_be(false)
expect(result.session_id).to_equal("s0")
expect(result.conversation.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(result.conversation[0].content).to_equal("keep this")
expect(tui_transcript_len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### should run a model turn through the production submission path

- should run a model turn through the production submission path
- Verify: should run a model turn through the production submission path
   - Expected: result.conversation.len() equals `2`
   - Expected: result.ui.input.value equals ``
   - Expected: tui_transcript_line_text(0) equals `You: hello`
   - Expected: SUBMISSION_RESPONDER_CALLS equals `1`
   - Expected: SUBMISSION_PERSIST_CALLS equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should run a model turn through the production submission path")
step("Verify: should run a model turn through the production submission path")
tui_transcript_reset()
_reset_submission_call_counts()
val ui = make_chat_tui_with_status(
    "llm_caret - dummy",
    "provider=dummy model=dummy-hello session=s0"
)
val result = run_chat_tui_submission(
    ui, [], "s0", "hello", default_policy("build/tmp/caret-tui-unit"),
    _submission_response, _test_hooks()
)
expect(result.running).to_be(true)
expect(result.submitted_to_model).to_be(true)
expect(result.conversation.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(result.ui.input.value).to_equal("")
expect(tui_transcript_line_text(0)).to_equal("You: hello")
expect(tui_transcript_line_text(1)).to_equal(
    "Assistant: submission reply"
)
expect(SUBMISSION_RESPONDER_CALLS).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(SUBMISSION_PERSIST_CALLS).to_equal(1)  # oracle: 1 — named expected value from the requirement
```

</details>

#### should keep the new-session confirmation after transcript reset

- should keep the new-session confirmation after transcript reset
- Verify: should keep the new-session confirmation after transcript reset
   - Expected: result.session_id equals `s-new`
   - Expected: result.conversation.len() equals `0`
   - Expected: tui_transcript_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should keep the new-session confirmation after transcript reset")
step("Verify: should keep the new-session confirmation after transcript reset")
tui_transcript_reset()
render_turn("user", "old conversation")
val ui = make_chat_tui_with_status(
    "llm_caret - dummy",
    "provider=dummy model=dummy-hello session=s0"
)
val result = run_chat_tui_submission(
    ui, [new_user_message("old conversation")], "s0", "/new",
    default_policy("build/tmp/caret-tui-unit"),
    _submission_response, _test_hooks()
)
expect(result.session_id).to_equal("s-new")
expect(result.conversation.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(tui_transcript_len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(tui_transcript_line_text(0)).to_equal(
    "System: started a new conversation"
)
```

</details>

#### should restore provider model session history and confirmation together

- should restore provider model session history and confirmation together
- Verify: should restore provider model session history and confirmation together
   - Expected: result.session_id equals `abc`
   - Expected: result.ui.title equals `llm_caret - claude_cli`
   - Expected: tui_transcript_line_text(0) equals `You: restored`
   - Expected: tui_transcript_line_text(1) equals `System: resumed abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should restore provider model session history and confirmation together")
step("Verify: should restore provider model session history and confirmation together")
tui_transcript_reset()
val ui = make_chat_tui_with_status(
    "llm_caret - dummy",
    "provider=dummy model=dummy-hello session=s0"
)
val result = run_chat_tui_submission(
    ui, [], "s0", "/resume abc",
    default_policy("build/tmp/caret-tui-unit"),
    _submission_response, _test_hooks()
)
expect(result.session_id).to_equal("abc")
expect(result.ui.title).to_equal("llm_caret - claude_cli")
expect(result.ui.status).to_equal(
    "provider=claude_cli model=sonnet session=abc"
)
expect(tui_transcript_line_text(0)).to_equal("You: restored")
expect(tui_transcript_line_text(1)).to_equal("System: resumed abc")
```

</details>

#### should preserve conversation and session when resume fails

- should preserve conversation and session when resume fails
- Verify: should preserve conversation and session when resume fails
   - Expected: result.session_id equals `s0`
   - Expected: result.conversation.len() equals `1`
   - Expected: result.conversation[0].role equals `user`
   - Expected: result.conversation[0].content equals `keep this`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should preserve conversation and session when resume fails")
step("Verify: should preserve conversation and session when resume fails")
tui_transcript_reset()
val original = [new_user_message("keep this")]
val result = run_chat_tui_submission(
    make_chat_tui("llm_caret"), original, "s0",
    "/resume missing-id",
    default_policy("build/tmp/caret-tui-unit"),
    _submission_response, _test_hooks_missing()
)
expect(result.running).to_be(true)
expect(result.submitted_to_model).to_be(false)
expect(result.session_id).to_equal("s0")
expect(result.conversation.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(result.conversation[0].role).to_equal("user")
expect(result.conversation[0].content).to_equal("keep this")
expect(tui_transcript_line_text(0)).to_equal(
    "System: no saved session 'missing-id'"
)
```

</details>

#### should keep unknown slash input out of the model conversation

- should keep unknown slash input out of the model conversation
- Verify: should keep unknown slash input out of the model conversation
   - Expected: result.session_id equals `s0`
   - Expected: result.conversation.len() equals `1`
   - Expected: result.conversation[0].role equals `user`
   - Expected: result.conversation[0].content equals `keep this`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should keep unknown slash input out of the model conversation")
step("Verify: should keep unknown slash input out of the model conversation")
tui_transcript_reset()
val original = [new_user_message("keep this")]
val result = run_chat_tui_submission(
    make_chat_tui("llm_caret"), original, "s0",
    "/not-registered secret-argument",
    default_policy("build/tmp/caret-tui-unit"),
    _submission_response, _test_hooks()
)
expect(result.submitted_to_model).to_be(false)
expect(result.session_id).to_equal("s0")
expect(result.conversation.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(result.conversation[0].role).to_equal("user")
expect(result.conversation[0].content).to_equal("keep this")
expect(tui_transcript_line_text(0)).to_contain("Unknown command")
expect(tui_transcript_line_text(0).contains(
    "secret-argument"
)).to_be(false)
```

</details>

#### should render accepted promptless commands without model submission

- should render accepted promptless commands without model submission
- Load the accepted promptless command aliases
- Dispatch the command through the shipped Caret path
- Check canonical output and zero model submission
   - Expected: SUBMISSION_RESPONDER_CALLS equals `0`
   - Expected: SUBMISSION_PERSIST_CALLS equals `0`
   - Expected: result.session_id equals `s0`
   - Expected: result.conversation.len() equals `1`
   - Expected: result.conversation[0].role equals `user`
   - Expected: result.conversation[0].content equals `keep this`
   - Expected: result.ui.title equals `original_ui.title`
   - Expected: result.ui.status equals `original_ui.status`
   - Expected: result.ui.input.value equals ``
   - Expected: tui_transcript_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should render accepted promptless commands without model submission")
step("Load the accepted promptless command aliases")
val cases = setup_promptless_command_cases()
val original = [new_user_message("keep this")]
val original_ui = make_chat_tui_with_status(
    "llm_caret - dummy",
    "provider=dummy model=dummy-hello session=s0"
)
step("Dispatch the command through the shipped Caret path")
step("Check canonical output and zero model submission")
for case in cases:
    tui_transcript_reset()
    _reset_submission_call_counts()
    val result = run_chat_tui_submission(
        original_ui, original, "s0", case.input,
        default_policy("build/tmp/caret-tui-unit"),
        _submission_response, _test_hooks()
    )
    expect(result.running).to_be(true)
    expect(result.submitted_to_model).to_be(false)
    expect(SUBMISSION_RESPONDER_CALLS).to_equal(0)  # oracle: 0 — named expected value from the requirement
    expect(SUBMISSION_PERSIST_CALLS).to_equal(0)  # oracle: 0 — named expected value from the requirement
    expect(result.session_id).to_equal("s0")
    expect(result.conversation.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
    expect(result.conversation[0].role).to_equal("user")
    expect(result.conversation[0].content).to_equal("keep this")
    expect(result.ui.title).to_equal(original_ui.title)
    expect(result.ui.status).to_equal(original_ui.status)
    expect(result.ui.input.value).to_equal("")
    expect(tui_transcript_len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
    expect(tui_transcript_line_text(0)).to_equal(
        "System: " + case.expected_message
    )
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 62 |
| Active scenarios | 62 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
| Executed scenarios | 0 |
