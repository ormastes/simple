# Chat Tui Runtime Specification

> Tests covering REQ-LLM-CARET-TUI-HARDEN-009: frame and input behavior, REQ-LLM-CARET-HIDDEN-008: plain hidden-command admission, REQ-LLM-CARET-TUI-HARDEN-007: lifecycle and routing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chat Tui Runtime Specification

## Scenarios

### REQ-LLM-CARET-TUI-HARDEN-009: frame and input behavior

#### should clamp inner content height for undersized terminals

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LLM-CARET-TUI-HARDEN-009
# @req REQ-LLM-CARET-HIDDEN-008
# @req REQ-LLM-CARET-TUI-HARDEN-007
```

</details>

#### should derive normal inner content height from the supplied rows

- should derive normal inner content height from the supplied rows
- Calculate a normal production frame height
   - Expected: _inner_height(24) equals `19`
   - Expected: _inner_height(40) equals `35`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should derive normal inner content height from the supplied rows")
step("Calculate a normal production frame height")
expect(_inner_height(24)).to_equal(19)
expect(_inner_height(40)).to_equal(35)
```

</details>

#### should draw a frame from one geometry snapshot and flush once

- should draw a frame from one geometry snapshot and flush once
- Render one production frame through deterministic CaretIo
   - Expected: IO_SIZE_CALLS equals `1`
   - Expected: IO_FLUSH_CALLS equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should draw a frame from one geometry snapshot and flush once")
step("Render one production frame through deterministic CaretIo")
_reset_fakes()
IO_COLS = 72
IO_ROWS = 20
_draw_frame(make_chat_tui("Caret"), _fake_io())
expect(IO_SIZE_CALLS).to_equal(1)
expect(IO_FLUSH_CALLS).to_equal(1)
expect(IO_DRAW_CALLS).to_be_greater_than(3)
expect(IO_EVENTS).to_start_with("clear|size|")
expect(IO_EVENTS).to_end_with("flush|")
```

</details>

#### should keep every draw within undersized terminal rows

- should keep every draw within undersized terminal rows
- Configure a terminal below the minimum layout height
- Draw one bounded frame through deterministic CaretIo
- Check every draw row stays inside the terminal snapshot
   - Expected: IO_SIZE_CALLS equals `1`
   - Expected: IO_FLUSH_CALLS equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should keep every draw within undersized terminal rows")
step("Configure a terminal below the minimum layout height")
_reset_fakes()
IO_COLS = 40
IO_ROWS = 5

step("Draw one bounded frame through deterministic CaretIo")
_draw_frame(make_chat_tui("Caret"), _fake_io())

step("Check every draw row stays inside the terminal snapshot")
expect(IO_SIZE_CALLS).to_equal(1)
expect(IO_DRAW_ROWS.len()).to_be_greater_than(0)
for row in IO_DRAW_ROWS:
    expect(row).to_be_greater_than(-1)
    expect(row).to_be_less_than(IO_ROWS)
expect(IO_FLUSH_CALLS).to_equal(1)
```

</details>

#### should edit and submit bytes through the production line reader

- should edit and submit bytes through the production line reader
- Type ab, move left, insert X, and submit
   - Expected: result.1 equals `aXb`
   - Expected: result.2 equals `0`
   - Expected: result.0.input.value equals `aXb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should edit and submit bytes through the production line reader")
step("Type ab, move left, insert X, and submit")
_reset_fakes()
IO_BYTES = [97, 98, 27, 91, 68, 88, 13]
val result = _read_line(make_chat_tui("Caret"), _fake_io())
expect(result.1).to_equal("aXb")
expect(result.2).to_equal(0)
expect(result.0.input.value).to_equal("aXb")
```

</details>

#### should report EOF without submitting partial input

- should report EOF without submitting partial input
- End input after one unsubmitted byte
   - Expected: result.1 equals ``
   - Expected: result.2 equals `1`
   - Expected: result.0.input.value equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should report EOF without submitting partial input")
step("End input after one unsubmitted byte")
_reset_fakes()
IO_BYTES = [120, -1]
val result = _read_line(make_chat_tui("Caret"), _fake_io())
expect(result.1).to_equal("")
expect(result.2).to_equal(1)
expect(result.0.input.value).to_equal("x")
```

</details>

#### should route page controls without inserting them into input

- should route page controls without inserting them into input
- Page away from and back to the transcript tail
   - Expected: result.1 equals ``
   - Expected: result.0.input.value equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should route page controls without inserting them into input")
step("Page away from and back to the transcript tail")
_reset_fakes()
IO_ROWS = 8
for line in ["0", "1", "2", "3", "4", "5", "6", "7"]:
    render_turn("assistant", line)
IO_BYTES = [16, 14, 13]
val result = _read_line(make_chat_tui("Caret"), _fake_io())
expect(result.1).to_equal("")
expect(result.0.input.value).to_equal("")
expect(is_scrolled()).to_be(false)
```

</details>

<details>
<summary>Advanced: should stop the plain loop on EOF without terminal mutation</summary>

#### should stop the plain loop on EOF without terminal mutation

- should stop the plain loop on EOF without terminal mutation
- Run the production plain loop with exhausted line input
   - Expected: result.mode equals `plain`
   - Expected: result.exit_reason equals `eof`
   - Expected: IO_BEGIN_CALLS equals `0`
   - Expected: IO_END_CALLS equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should stop the plain loop on EOF without terminal mutation")
step("Run the production plain loop with exhausted line input")
_reset_fakes()
val result = run_chat_plain(
    _policy(), _responder, _hooks(), [], _fake_io()
)
expect(result.mode).to_equal("plain")
expect(result.ok).to_be(true)
expect(result.exit_reason).to_equal("eof")
expect(IO_BEGIN_CALLS).to_equal(0)
expect(IO_END_CALLS).to_equal(0)
```

</details>


</details>

#### should ignore blank plain input without discarding later commands

- should ignore blank plain input without discarding later commands
- Queue blank input before a valid plain turn
- Run the production plain loop through deterministic CaretIo
- Check blank input was ignored and the later turn persisted
   - Expected: result.mode equals `plain`
   - Expected: result.exit_reason equals `command_exit`
   - Expected: IO_LINE_INDEX equals `4`
   - Expected: IO_LINE_INDEX equals `IO_LINES.len()`
   - Expected: RESPONDER_CALLS equals `1`
   - Expected: HOOK_PERSIST_COUNT equals `1`
   - Expected: HOOK_PERSIST_SESSION equals `fixture-session`
   - Expected: HOOK_PERSIST_MESSAGES equals `2`
   - Expected: IO_BEGIN_CALLS equals `0`
   - Expected: IO_END_CALLS equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should ignore blank plain input without discarding later commands")
step("Queue blank input before a valid plain turn")
_reset_fakes()
IO_LINES = ["", "   ", "hello", "/exit"]

step("Run the production plain loop through deterministic CaretIo")
val result = run_chat_plain(
    _policy(), _responder, _hooks(), [], _fake_io()
)

step("Check blank input was ignored and the later turn persisted")
expect(result.mode).to_equal("plain")
expect(result.ok).to_be(true)
expect(result.exit_reason).to_equal("command_exit")
expect(IO_LINE_INDEX).to_equal(4)
expect(IO_LINE_INDEX).to_equal(IO_LINES.len())
expect(RESPONDER_CALLS).to_equal(1)
expect(HOOK_PERSIST_COUNT).to_equal(1)
expect(HOOK_PERSIST_SESSION).to_equal("fixture-session")
expect(HOOK_PERSIST_MESSAGES).to_equal(2)
expect(IO_OUTPUT).to_contain("Assistant: fixture reply")
expect(IO_BEGIN_CALLS).to_equal(0)
expect(IO_END_CALLS).to_equal(0)
```

</details>

#### should process plain model commands and persist model turns

- should process plain model commands and persist model turns
- Switch model, submit one turn, and exit the production plain loop
   - Expected: result.exit_reason equals `command_exit`
   - Expected: HOOK_MODEL equals `sonnet`
   - Expected: HOOK_PERSIST_COUNT equals `1`
   - Expected: HOOK_PERSIST_SESSION equals `fixture-session`
   - Expected: HOOK_PERSIST_MESSAGES equals `2`
   - Expected: RESPONDER_CALLS equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should process plain model commands and persist model turns")
step("Switch model, submit one turn, and exit the production plain loop")
_reset_fakes()
IO_LINES = ["/model sonnet", "hello", "/exit"]
val result = run_chat_plain(
    _policy(), _responder, _hooks(), [], _fake_io()
)
expect(result.exit_reason).to_equal("command_exit")
expect(HOOK_MODEL).to_equal("sonnet")
expect(HOOK_PERSIST_COUNT).to_equal(1)
expect(HOOK_PERSIST_SESSION).to_equal("fixture-session")
expect(HOOK_PERSIST_MESSAGES).to_equal(2)
expect(IO_OUTPUT).to_contain("model set to sonnet")
expect(IO_OUTPUT).to_contain("Assistant: fixture reply")
expect(RESPONDER_CALLS).to_equal(1)
```

</details>

#### should dispatch accepted promptless aliases without model submission

- should dispatch accepted promptless aliases without model submission
- Load the accepted promptless command aliases
- Dispatch the command through the shipped Caret path
- Check canonical output and zero model submission


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should dispatch accepted promptless aliases without model submission")
step("Load the accepted promptless command aliases")
val cases = setup_promptless_command_cases()
_reset_fakes()
IO_LINES = [
    cases[0].input,
    cases[1].input,
    cases[2].input,
    cases[3].input,
    "/exit"
]

step("Dispatch the command through the shipped Caret path")
val result = run_chat_plain(
    _policy(), _responder, _hooks(), [], _fake_io()
)

step("Check canonical output and zero model submission")
check_promptless_dispatch(cases, result)
```

</details>

### REQ-LLM-CARET-HIDDEN-008: plain hidden-command admission

#### should conceal hidden canonical and alias commands and reject disabled aliases

- should conceal hidden canonical and alias commands and reject disabled aliases
- Queue hidden and disabled command spellings with the hidden gate off
- Dispatch the production plain loop through injected CaretIo
- Check hidden membership stays concealed and no model or terminal work occurs
   - Expected: result.mode equals `plain`
   - Expected: result.exit_reason equals `command_exit`
   - Expected: HOOK_HIDDEN_CALLS equals `0`
   - Expected: HOOK_HIDDEN_NAME equals ``
   - Expected: HOOK_HIDDEN_ARG equals ``
   - Expected: RESPONDER_CALLS equals `0`
   - Expected: HOOK_PERSIST_COUNT equals `0`
   - Expected: HOOK_PERSIST_SESSION equals ``
   - Expected: HOOK_PERSIST_MESSAGES equals `0`
   - Expected: IO_BEGIN_CALLS equals `0`
   - Expected: IO_END_CALLS equals `0`
   - Expected: IO_SIZE_CALLS equals `0`
   - Expected: IO_DRAW_CALLS equals `0`
   - Expected: IO_FLUSH_CALLS equals `0`
   - Expected: IO_BYTE_INDEX equals `0`
   - Expected: IO_LINE_INDEX equals `IO_LINES.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should conceal hidden canonical and alias commands and reject disabled aliases")
step("Queue hidden and disabled command spellings with the hidden gate off")
_reset_fakes()
IO_LINES = [
    "/debug-tool-call fixture-envelope",
    "/debug_tool_call fixture-envelope",
    "/remote_setup",
    "/exit"
]

step("Dispatch the production plain loop through injected CaretIo")
val result = run_chat_plain(
    _policy(), _responder, _hooks(), [], _fake_io()
)

step("Check hidden membership stays concealed and no model or terminal work occurs")
expect(result.mode).to_equal("plain")
expect(result.ok).to_be(true)
expect(result.exit_reason).to_equal("command_exit")
expect(IO_OUTPUT).to_equal(
    "> Unknown command: /debug-tool-call (try /help)\n" +
    "> Unknown command: /debug_tool_call (try /help)\n" +
    "> Command disabled: /remote_setup\n" +
    "> "
)
expect(HOOK_HIDDEN_CALLS).to_equal(0)
expect(HOOK_HIDDEN_NAME).to_equal("")
expect(HOOK_HIDDEN_ARG).to_equal("")
expect(RESPONDER_CALLS).to_equal(0)
expect(HOOK_PERSIST_COUNT).to_equal(0)
expect(HOOK_PERSIST_SESSION).to_equal("")
expect(HOOK_PERSIST_MESSAGES).to_equal(0)
expect(IO_BEGIN_CALLS).to_equal(0)
expect(IO_END_CALLS).to_equal(0)
expect(IO_SIZE_CALLS).to_equal(0)
expect(IO_DRAW_CALLS).to_equal(0)
expect(IO_FLUSH_CALLS).to_equal(0)
expect(IO_BYTE_INDEX).to_equal(0)
expect(IO_LINE_INDEX).to_equal(IO_LINES.len())
```

</details>

### REQ-LLM-CARET-TUI-HARDEN-007: lifecycle and routing

#### should compensate setup failures without drawing model calls or persistence

- should compensate setup failures without drawing model calls or persistence
- Reject each typed setup failure through the production TUI loop
   - Expected: result.mode equals `tui`
   - Expected: result.exit_reason equals `terminal-setup-failed`
   - Expected: result.error equals `"failed " + phase`
   - Expected: IO_BEGIN_CALLS equals `1`
   - Expected: IO_END_CALLS equals `1`
   - Expected: IO_DRAW_CALLS equals `0`
   - Expected: IO_OUTPUT equals ``
   - Expected: RESPONDER_CALLS equals `0`
   - Expected: HOOK_PERSIST_COUNT equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should compensate setup failures without drawing model calls or persistence")
step("Reject each typed setup failure through the production TUI loop")
for phase in ["raw-mode", "alternate-screen", "cursor-hide"]:
    _reset_fakes()
    IO_BEGIN_OK = false
    IO_BEGIN_PHASE = phase
    IO_BEGIN_ERROR = "failed " + phase
    val result = run_chat_tui(
        make_chat_tui("Caret"), _policy(), _responder, _hooks(), [],
        _fake_io()
    )
    expect(result.mode).to_equal("tui")
    expect(result.ok).to_be(false)
    expect(result.exit_reason).to_equal("terminal-setup-failed")
    expect(result.error).to_equal("failed " + phase)
    expect(IO_BEGIN_CALLS).to_equal(1)
    expect(IO_END_CALLS).to_equal(1)
    expect(IO_DRAW_CALLS).to_equal(0)
    expect(IO_OUTPUT).to_equal("")
    expect(RESPONDER_CALLS).to_equal(0)
    expect(HOOK_PERSIST_COUNT).to_equal(0)
```

</details>

#### should end the TUI exactly once and emit the success footer

- should end the TUI exactly once and emit the success footer
- Exit by command after entering the full-screen production loop
   - Expected: result.exit_reason equals `command_exit`
   - Expected: IO_BEGIN_CALLS equals `1`
   - Expected: IO_END_CALLS equals `1`
   - Expected: IO_OUTPUT equals `chat session ended\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should end the TUI exactly once and emit the success footer")
step("Exit by command after entering the full-screen production loop")
_reset_fakes()
IO_BYTES = _exit_command_bytes()
val result = run_chat_tui(
    make_chat_tui("Caret"), _policy(), _responder, _hooks(), [],
    _fake_io()
)
expect(result.ok).to_be(true)
expect(result.exit_reason).to_equal("command_exit")
expect(IO_BEGIN_CALLS).to_equal(1)
expect(IO_END_CALLS).to_equal(1)
expect(IO_EVENTS).to_start_with("begin_tui|")
expect(IO_EVENTS).to_end_with("end_tui|emit|")
expect(IO_OUTPUT).to_equal("chat session ended\n")
```

</details>

#### should report cleanup failure without a success footer

- should report cleanup failure without a success footer
- Fail compensating terminal cleanup after a command exit
   - Expected: result.exit_reason equals `terminal-cleanup-failed`
   - Expected: result.error equals `failed to restore terminal raw mode`
   - Expected: IO_BEGIN_CALLS equals `1`
   - Expected: IO_END_CALLS equals `1`
   - Expected: IO_OUTPUT equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should report cleanup failure without a success footer")
step("Fail compensating terminal cleanup after a command exit")
_reset_fakes()
IO_END_OK = false
IO_END_PHASE = "raw-mode"
IO_END_ERROR = "failed to restore terminal raw mode"
IO_BYTES = _exit_command_bytes()
val result = run_chat_tui(
    make_chat_tui("Caret"), _policy(), _responder, _hooks(), [],
    _fake_io()
)
expect(result.ok).to_be(false)
expect(result.exit_reason).to_equal("terminal-cleanup-failed")
expect(result.error).to_equal("failed to restore terminal raw mode")
expect(IO_BEGIN_CALLS).to_equal(1)
expect(IO_END_CALLS).to_equal(1)
expect(IO_OUTPUT).to_equal("")
```

</details>

#### should end exactly once for command control and EOF exits

- should end exactly once for command control and EOF exits
- Exercise every normal TUI exit through the shared lifecycle
   - Expected: IO_BEGIN_CALLS equals `1`
   - Expected: IO_END_CALLS equals `1`
   - Expected: IO_OUTPUT equals `chat session ended\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should end exactly once for command control and EOF exits")
step("Exercise every normal TUI exit through the shared lifecycle")
for input in [_exit_command_bytes(), [3], [4], [-1]]:
    _reset_fakes()
    IO_BYTES = input
    val result = run_chat_tui(
        make_chat_tui("Caret"), _policy(), _responder, _hooks(), [],
        _fake_io()
    )
    expect(result.ok).to_be(true)
    expect(IO_BEGIN_CALLS).to_equal(1)
    expect(IO_END_CALLS).to_equal(1)
    expect(IO_OUTPUT).to_equal("chat session ended\n")
```

</details>

#### should force TUI routing without a tty

- should force TUI routing without a tty
- Request TUI mode while the injected tty probe is false
   - Expected: result.mode equals `tui`
   - Expected: IO_BEGIN_CALLS equals `1`
   - Expected: IO_END_CALLS equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should force TUI routing without a tty")
step("Request TUI mode while the injected tty probe is false")
_reset_fakes()
IO_TTY = false
IO_BYTES = _exit_command_bytes()
val result = caret_chat(
    make_chat_tui("Caret"), _policy(), _responder, "tui",
    _hooks(), [], _fake_io()
)
expect(result.mode).to_equal("tui")
expect(IO_BEGIN_CALLS).to_equal(1)
expect(IO_END_CALLS).to_equal(1)
```

</details>

#### should force plain routing on a tty

- should force plain routing on a tty
- Request plain mode while the injected tty probe is true
   - Expected: result.mode equals `plain`
   - Expected: IO_BEGIN_CALLS equals `0`
   - Expected: IO_END_CALLS equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should force plain routing on a tty")
step("Request plain mode while the injected tty probe is true")
_reset_fakes()
IO_TTY = true
IO_LINES = ["/exit"]
val result = caret_chat(
    make_chat_tui("Caret"), _policy(), _responder, "plain",
    _hooks(), [], _fake_io()
)
expect(result.mode).to_equal("plain")
expect(IO_BEGIN_CALLS).to_equal(0)
expect(IO_END_CALLS).to_equal(0)
```

</details>

#### should automatically route tty input to TUI

- should automatically route tty input to TUI
- Select automatic mode with an injected tty
   - Expected: result.mode equals `tui`
   - Expected: IO_BEGIN_CALLS equals `1`
   - Expected: IO_END_CALLS equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should automatically route tty input to TUI")
step("Select automatic mode with an injected tty")
_reset_fakes()
IO_TTY = true
IO_BYTES = [3]
val result = caret_chat(
    make_chat_tui("Caret"), _policy(), _responder, "auto",
    _hooks(), [], _fake_io()
)
expect(result.mode).to_equal("tui")
expect(IO_EVENTS).to_start_with("is_tty|begin_tui|")
expect(IO_BEGIN_CALLS).to_equal(1)
expect(IO_END_CALLS).to_equal(1)
```

</details>

#### should automatically route non-tty input to plain mode

- should automatically route non-tty input to plain mode
- Select automatic mode without an injected tty
   - Expected: result.mode equals `plain`
   - Expected: IO_BEGIN_CALLS equals `0`
   - Expected: IO_END_CALLS equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should automatically route non-tty input to plain mode")
step("Select automatic mode without an injected tty")
_reset_fakes()
IO_TTY = false
IO_LINES = ["/exit"]
val result = caret_chat(
    make_chat_tui("Caret"), _policy(), _responder, "auto",
    _hooks(), [], _fake_io()
)
expect(result.mode).to_equal("plain")
expect(IO_EVENTS).to_start_with("is_tty|emit|")
expect(IO_BEGIN_CALLS).to_equal(0)
expect(IO_END_CALLS).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering REQ-LLM-CARET-TUI-HARDEN-009: frame and input behavior, REQ-LLM-CARET-HIDDEN-008: plain hidden-command admission, REQ-LLM-CARET-TUI-HARDEN-007: lifecycle and routing.
- REQ-LLM-CARET-TUI-HARDEN-009: frame and input behavior
- REQ-LLM-CARET-HIDDEN-008: plain hidden-command admission
- REQ-LLM-CARET-TUI-HARDEN-007: lifecycle and routing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
- `REQ-LLM-CARET-TUI-HARDEN-009`
- `REQ-LLM-CARET-HIDDEN-008`
- `REQ-LLM-CARET-TUI-HARDEN-007`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `912d0f74b765ea75d6b91abc4f07e7bf967ad2148c1a2337d8de74ccf2b67c0d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `912d0f74b765ea75d6b91abc4f07e7bf967ad2148c1a2337d8de74ccf2b67c0d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `912d0f74b765ea75d6b91abc4f07e7bf967ad2148c1a2337d8de74ccf2b67c0d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **80/100**; blockers: **0**.

SSpec documentization score: 80/100
source: test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/chat_tui_runtime_spec.md (current)
findings: 13 blockers: 0
  narrative=100 structure=60 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/llm_caret/chat_tui_runtime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/chat_tui_runtime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 48 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl:313:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'should clamp inner content height for undersized terminals' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl:313:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should clamp inner content height for undersized terminals' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl:325:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should derive normal inner content height from the supplied rows' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl:325:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should derive normal inner content height from the supplied rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl:332:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should draw a frame from one geometry snapshot and flush once' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl:332:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should draw a frame from one geometry snapshot and flush once' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl:346:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep every draw within undersized terminal rows' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl:346:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep every draw within undersized terminal rows' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl:365:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should edit and submit bytes through the production line reader' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl:376:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report EOF without submitting partial input' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
