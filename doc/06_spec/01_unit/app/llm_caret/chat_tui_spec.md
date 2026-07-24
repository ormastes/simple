# LLM Caret Chat Tui Unit Spec

> Source-synchronized unit manual. The current self-hosted SSpec runner is
> blocked before trustworthy scenario execution, so this document records
> 64 active scenarios and 0 executed scenarios.

| Tests | Active | Skipped | Pending | Executed |
|------:|-------:|--------:|--------:|---------:|
| 64 | 64 | 0 | 0 | 0 |

**Executable source:** `test/01_unit/app/llm_caret/chat_tui_spec.spl`

## should label user and assistant turns distinctly

**Group:** TUI pure formatting

<details>
<summary>Executable SSpec</summary>

```simple
expect(tui_role_label("user")).to_equal("You")
expect(tui_role_label("assistant")).to_equal("Assistant")
```

</details>

## should format a turn line with its role label

**Group:** TUI pure formatting

<details>
<summary>Executable SSpec</summary>

```simple
expect(format_turn_line("user", "hello")).to_equal("You: hello")
expect(format_turn_line("assistant", "hi")).to_equal("Assistant: hi")
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
expect(us.fg == asst.fg).to_be(false)
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
val previous = env_get("TERM")
expect(env_set("TERM", "dumb")).to_be(true)
expect(caret_is_tty()).to_be(false)
expect(env_set("TERM", "xterm-256color")).to_be(true)
expect(caret_is_tty()).to_be(true)
_restore_term(previous)
```

</details>

## should append a styled user turn to the transcript

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

```simple
val p = default_policy(WS_ROOT)
val result = run_agent_loop(p, [new_user_message("go")], _one_tool, 25)
# initial user turn + tool_result turn + final assistant turn = 3.
# Before the fix, callers only had `initial + [final_text]` (len 2)
# and the tool_result turn was silently dropped between top-level
# calls - this is the exact gap the guide's M2 milestone flagged.
expect(result.final_transcript.len()).to_equal(3)
expect(result.final_transcript[1].content).to_contain("tool_result")
```

</details>

## should render a plain single-line turn exactly as format_turn_line would

**Group:** Markdown-lite rendering

<details>
<summary>Executable SSpec</summary>

```simple
tui_transcript_reset()
render_turn("assistant", "hi")
expect(tui_transcript_len()).to_equal(1)
expect(tui_transcript_line_text(0)).to_equal("Assistant: hi")
```

</details>

## should split multi-line content into one transcript line per source line

**Group:** Markdown-lite rendering

<details>
<summary>Executable SSpec</summary>

```simple
tui_transcript_reset()
render_turn("assistant", "line one\nline two")
expect(tui_transcript_len()).to_equal(2)
expect(tui_transcript_line_text(0)).to_equal("Assistant: line one")
expect(tui_transcript_line_text(1)).to_equal("line two")
```

</details>

## should detect fenced code block markers

**Group:** Markdown-lite rendering

<details>
<summary>Executable SSpec</summary>

```simple
expect(is_fence_line("```")).to_be(true)
expect(is_fence_line("```python")).to_be(true)
expect(is_fence_line("plain text")).to_be(false)
```

</details>

## should indent bullet lines and leave others untouched

**Group:** Markdown-lite rendering

<details>
<summary>Executable SSpec</summary>

```simple
expect(bullet_indent("- item")).to_equal("  - item")
expect(bullet_indent("* item")).to_equal("  * item")
expect(bullet_indent("plain")).to_equal("plain")
```

</details>

## should render a fenced code block dim with indentation preserved

**Group:** Markdown-lite rendering

<details>
<summary>Executable SSpec</summary>

```simple
tui_transcript_reset()
render_turn("assistant", "```\n  indented code\n```")
expect(tui_transcript_len()).to_equal(3)
expect(tui_transcript_line_text(1)).to_equal("  indented code")
```

</details>

## should split inline code spans into separate segments

**Group:** Markdown-lite rendering

<details>
<summary>Executable SSpec</summary>

```simple
val segs = inline_code_segments("run `cmd` now", tui_default_style())
expect(segs.len()).to_equal(3)
expect(segs[0].content).to_equal("run ")
expect(segs[1].content).to_equal("cmd")
expect(segs[2].content).to_equal(" now")
```

</details>

## should markdown_turn_lines prefixes only the first line with the role label

**Group:** Markdown-lite rendering

<details>
<summary>Executable SSpec</summary>

```simple
val lines = markdown_turn_lines("user", "a\nb")
expect(lines.len()).to_equal(2)
```

</details>

## should auto-follow (-1) shows the tail when content exceeds the viewport

**Group:** Scrollback window (visible_window)

<details>
<summary>Executable SSpec</summary>

```simple
val (start, end) = visible_window(10, 4, -1)
expect(start).to_equal(6)
expect(end).to_equal(10)
```

</details>

## should auto-follow shows everything when content fits the viewport

**Group:** Scrollback window (visible_window)

<details>
<summary>Executable SSpec</summary>

```simple
val (start, end) = visible_window(3, 4, -1)
expect(start).to_equal(0)
expect(end).to_equal(3)
```

</details>

## should a fixed scroll_top clamps to the valid range

**Group:** Scrollback window (visible_window)

<details>
<summary>Executable SSpec</summary>

```simple
val (start, end) = visible_window(10, 4, 100)
expect(start).to_equal(6)
```

</details>

## should a fixed scroll_top of 0 shows the very top

**Group:** Scrollback window (visible_window)

<details>
<summary>Executable SSpec</summary>

```simple
val (start, end) = visible_window(10, 4, 0)
expect(start).to_equal(0)
expect(end).to_equal(4)
```

</details>

## should be not scrolled by default

**Group:** Scroll paging (Ctrl-P/Ctrl-N)

<details>
<summary>Executable SSpec</summary>

```simple
tui_transcript_reset()
expect(is_scrolled()).to_be(false)
```

</details>

## should page up away from auto-follow, and resume after enough pages down

**Group:** Scroll paging (Ctrl-P/Ctrl-N)

<details>
<summary>Executable SSpec</summary>

```simple
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

## should decode CSI and SS3 arrows without leaking printable bytes

**Group:** ANSI raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
expect(_decode_raw_bytes([27, 91, 65])).to_equal(("up", ""))
expect(_decode_raw_bytes([27, 91, 66])).to_equal(("down", ""))
expect(_decode_raw_bytes([27, 91, 67])).to_equal(("right", ""))
expect(_decode_raw_bytes([27, 91, 68])).to_equal(("left", ""))
expect(_decode_raw_bytes([27, 79, 67])).to_equal(("right", ""))
```

</details>

## should decode direct and numeric home and end sequences

**Group:** ANSI raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
expect(_decode_raw_bytes([27, 91, 72])).to_equal(("home", ""))
expect(_decode_raw_bytes([27, 91, 70])).to_equal(("end", ""))
expect(_decode_raw_bytes([27, 91, 49, 126])).to_equal(("home", ""))
expect(_decode_raw_bytes([27, 91, 52, 126])).to_equal(("end", ""))
expect(_decode_raw_bytes([27, 91, 55, 126])).to_equal(("home", ""))
expect(_decode_raw_bytes([27, 91, 56, 126])).to_equal(("end", ""))
```

</details>

## should decode every supported SS3 navigation key

**Group:** ANSI raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
expect(_decode_raw_bytes([27, 79, 65])).to_equal(("up", ""))
expect(_decode_raw_bytes([27, 79, 66])).to_equal(("down", ""))
expect(_decode_raw_bytes([27, 79, 67])).to_equal(("right", ""))
expect(_decode_raw_bytes([27, 79, 68])).to_equal(("left", ""))
expect(_decode_raw_bytes([27, 79, 70])).to_equal(("end", ""))
expect(_decode_raw_bytes([27, 79, 72])).to_equal(("home", ""))
```

</details>

## should swallow modified and unknown ANSI sequences

**Group:** ANSI raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
expect(_decode_raw_bytes([27, 91, 49, 59, 53, 68])).to_equal(
    ("left", "")
)
expect(_decode_raw_bytes([27, 91, 51, 126])).to_equal(("", ""))
expect(_decode_raw_bytes([27, 120])).to_equal(("", ""))
```

</details>

## should preserve ordinary printable input after a completed sequence

**Group:** ANSI raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
expect(_decode_raw_bytes([27, 91, 67, 120])).to_equal(("right", "x"))
```

</details>

## should recover after abandoned and unknown escape sequences

**Group:** ANSI raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
expect(_decode_raw_bytes(
    [27, 91, 27, 91, 68, 120]
)).to_equal(("left", "x"))
expect(_decode_raw_bytes(
    [27, 91, 51, 126, 121]
)).to_equal(("", "y"))
```

</details>

## should apply decoded cursor keys without inserting escape bytes

**Group:** ANSI raw-key decoding

<details>
<summary>Executable SSpec</summary>

```simple
val edited = _apply_raw_bytes([
    97, 98, 99,
    27, 91, 68, 88,
    27, 91, 72, 62,
    27, 91, 70, 33
])
expect(edited).to_equal((">abXc!", 6))
```

</details>

## should recognize lines starting with /

**Group:** Slash command parsing

<details>
<summary>Executable SSpec</summary>

```simple
expect(is_slash_command("/help")).to_be(true)
expect(is_slash_command("hello")).to_be(false)
```

</details>

## should split a command and its argument

**Group:** Slash command parsing

<details>
<summary>Executable SSpec</summary>

```simple
val (cmd, arg) = parse_slash_command("/model gpt-4o")
expect(cmd).to_equal("model")
expect(arg).to_equal("gpt-4o")
```

</details>

## should split a command with no argument

**Group:** Slash command parsing

<details>
<summary>Executable SSpec</summary>

```simple
val (cmd, arg) = parse_slash_command("/help")
expect(cmd).to_equal("help")
expect(arg).to_equal("")
```

</details>

## should /help returns the help text

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
val r = dispatch_slash("help", "", _test_hooks())
expect(r.message).to_contain("/model <name>")
```

</details>

## should /exit sets exit=true

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
val r = dispatch_slash("exit", "", _test_hooks())
expect(r.exit).to_be(true)
```

</details>

## should /quit is an alias for /exit

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
val r = dispatch_slash("quit", "", _test_hooks())
expect(r.exit).to_be(true)
```

</details>

## should /new clears the conversation

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
val r = dispatch_slash("new", "", _test_hooks())
expect(r.new_conv).to_be(true)
expect(r.new_session_id).to_equal("s-new")
expect(r.status_session).to_equal("s-new")
```

</details>

## should apply a new conversation session to visible TUI status

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
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

## should /model with no argument is a usage error

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
val r = dispatch_slash("model", "", _test_hooks())
expect(r.message).to_contain("Usage")
```

</details>

## should /model <name> calls hooks.on_model

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
val r = dispatch_slash("model", "gpt-4o", _test_hooks())
expect(r.message).to_equal("model set to gpt-4o")
expect(r.status_model).to_equal("gpt-4o")
```

</details>

## should /provider <name> calls hooks.on_provider

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
val r = dispatch_slash("provider", "openai", _test_hooks())
expect(r.message).to_equal("provider set to openai")
expect(r.status_provider).to_equal("openai")
expect(r.status_model).to_equal("gpt-4o")
```

</details>

## should not refresh visible status after a rejected provider

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
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

## should apply provider and model changes to visible TUI status

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
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

## should /sessions calls hooks.on_sessions

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
val r = dispatch_slash("sessions", "", _test_hooks())
expect(r.message).to_contain("s1")
```

</details>

## should /resume <id> found: replaces the conversation

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
val r = dispatch_slash("resume", "abc", _test_hooks())
expect(r.replace_conv).to_be(true)
expect(r.new_session_id).to_equal("abc")
expect(r.status_session).to_equal("abc")
expect(r.status_provider).to_equal("claude_cli")
expect(r.status_model).to_equal("sonnet")
expect(r.loaded_messages.len()).to_equal(1)
```

</details>

## should apply a resumed session to visible TUI status

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
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

## should /resume <id> not found: reports it, does not replace

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
val r = dispatch_slash("resume", "missing-id", _test_hooks_missing())
expect(r.replace_conv).to_be(false)
expect(r.message).to_contain("no saved session")
expect(r.status_session).to_equal("")
```

</details>

## should report unknown /commands are reported, never silently sent to the model

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
val r = dispatch_slash("bogus", "", _test_hooks())
expect(r.message).to_contain("Unknown command")
expect(r.exit).to_be(false)
expect(r.new_conv).to_be(false)
expect(r.replace_conv).to_be(false)
```

</details>

## should reject hidden commands by default and execute an enabled fixture

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
val rejected = dispatch_slash(
    "debug-tool-call", "call-1", _test_hooks()
)
val unknown = dispatch_slash("not-registered", "", _test_hooks())
expect(rejected.message).to_equal(unknown.message)
val admitted = dispatch_slash(
    "debug-tool-call", "call-1", _test_hooks_hidden()
)
expect(admitted.message).to_equal(
    "hidden command executed: debug-tool-call call-1"
)
```

</details>

## should reject disabled registry commands under every fixture

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
val result = dispatch_slash(
    "remote-setup", "", _test_hooks_hidden()
)
expect(result.message).to_contain("Command disabled")
```

</details>

## should support help and conversation-reset aliases

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
expect(dispatch_slash("?", "", _test_hooks()).message).to_equal(
    slash_help_text()
)
expect(dispatch_slash("clear", "", _test_hooks()).new_conv).to_be(true)
expect(dispatch_slash("reset", "", _test_hooks()).new_conv).to_be(true)
```

</details>

## should distinguish recognized registry commands from unknown input

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
val known = dispatch_slash("config", "", _test_hooks())
val unknown = dispatch_slash("not-registered", "", _test_hooks())
expect(known.message).to_contain("not implemented in Caret")
expect(known.message).to_contain("/config")
expect(known.message == unknown.message).to_be(false)
```

</details>

## should enforce registry gates and canonical handlers through aliases

**Group:** Slash command dispatch

<details>
<summary>Executable SSpec</summary>

```simple
val hidden = dispatch_slash(
    "debug_tool_call", "payload", _test_hooks()
)
val unknown = dispatch_slash(
    "not-registered", "payload", _test_hooks()
)
expect(hidden.message).to_equal(unknown.message)

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

## should stop on the quit alias without mutating conversation state

**Group:** TUI submission state transition

<details>
<summary>Executable SSpec</summary>

```simple
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
expect(result.conversation.len()).to_equal(1)
expect(result.conversation[0].content).to_equal("keep this")
expect(tui_transcript_len()).to_equal(0)
```

</details>

## should run a model turn through the production submission path

**Group:** TUI submission state transition

<details>
<summary>Executable SSpec</summary>

```simple
tui_transcript_reset()
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
expect(result.conversation.len()).to_equal(2)
expect(result.ui.input.value).to_equal("")
expect(tui_transcript_line_text(0)).to_equal("You: hello")
expect(tui_transcript_line_text(1)).to_equal(
    "Assistant: submission reply"
)
```

</details>

## should keep the new-session confirmation after transcript reset

**Group:** TUI submission state transition

<details>
<summary>Executable SSpec</summary>

```simple
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
expect(result.conversation.len()).to_equal(0)
expect(tui_transcript_len()).to_equal(1)
expect(tui_transcript_line_text(0)).to_equal(
    "System: started a new conversation"
)
```

</details>

## should restore provider model session history and confirmation together

**Group:** TUI submission state transition

<details>
<summary>Executable SSpec</summary>

```simple
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

## should preserve conversation and session when resume fails

**Group:** TUI submission state transition

<details>
<summary>Executable SSpec</summary>

```simple
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
expect(result.conversation.len()).to_equal(1)
expect(result.conversation[0].role).to_equal("user")
expect(result.conversation[0].content).to_equal("keep this")
expect(tui_transcript_line_text(0)).to_equal(
    "System: no saved session 'missing-id'"
)
```

</details>

## should keep unknown slash input out of the model conversation

**Group:** TUI submission state transition

<details>
<summary>Executable SSpec</summary>

```simple
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
expect(result.conversation.len()).to_equal(1)
expect(result.conversation[0].role).to_equal("user")
expect(result.conversation[0].content).to_equal("keep this")
expect(tui_transcript_line_text(0)).to_contain("Unknown command")
expect(tui_transcript_line_text(0).contains(
    "secret-argument"
)).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 64 |
| Active scenarios | 64 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |
| Executed scenarios | 0 |
