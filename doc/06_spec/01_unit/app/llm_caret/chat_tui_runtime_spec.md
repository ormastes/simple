# LLM Caret TUI Runtime Seam Unit Spec

> Source-synchronized manual for deterministic direct-production coverage of
> `CaretIo`, `_draw_frame`, `_read_line`, `run_chat_tui`,
> `run_chat_plain`, and `caret_chat`. The fake I/O uses function fields only:
> it does not copy production algorithms, open a terminal, or declare runtime
> externs. Live PTY, panic, and signal evidence remain outside this unit scope.

| Tests | Active | Skipped | Pending | Executed |
|------:|-------:|--------:|--------:|---------:|
| 19 | 19 | 0 | 0 | 0 |

**Executable source:** `test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl`

## REQ-LLM-CARET-TUI-HARDEN-009: frame and input behavior

### should clamp inner content height for undersized terminals

**Step:** Calculate production frame heights below the minimum.

**Expected:** Rows 0, 1, and 5 all clamp to one inner content row.

### should derive normal inner content height from the supplied rows

**Step:** Calculate normal production frame heights.

**Expected:** The content height is derived from the supplied row snapshot.

### should draw a frame from one geometry snapshot and flush once

**Step:** Render one production frame through deterministic `CaretIo`.

**Expected:** The frame queries geometry once, draws visible rows, and flushes
exactly once.

### should edit and submit bytes through the production line reader

**Step:** Type `ab`, move left, insert `X`, and submit.

**Expected:** `_read_line` returns `aXb`, submit status 0, and the same widget
value.

### should report EOF without submitting partial input

**Step:** End input after one unsubmitted byte.

**Expected:** `_read_line` preserves the edited widget but returns no submitted
text and exit status 1.

### should route page controls without inserting them into input

**Step:** Page away from and back to the transcript tail.

**Expected:** Paging changes scroll state, inserts no control bytes, and returns
to auto-follow.

### should stop the plain loop on EOF without terminal mutation

**Step:** Run the production plain loop with exhausted line input.

**Expected:** The loop reports plain-mode EOF and never enters raw mode.

### should process plain model commands and persist model turns

**Step:** Switch model, submit one turn, and exit the production plain loop.

**Expected:** The model hook observes `sonnet`, one complete conversation is
persisted to the current session, and the visible model/assistant output is
emitted.

## REQ-LLM-CARET-TUI-HARDEN-007: lifecycle and routing

### should fail raw entry before alternate screen or cursor mutation

**Step:** Reject raw-mode acquisition through the production TUI loop.

**Expected:** The typed result reports `raw-mode-unavailable`; no alternate
screen, cursor, draw, cleanup, or success-output action occurs.

### should restore cursor screen and raw mode in lifecycle order

**Step:** Exit by command after entering the full-screen production loop.

**Expected:** Acquisition is raw, alternate screen, cursor hide. Cleanup is
cursor show, alternate-screen exit, raw restore, then the success message.

### should report restore failure after all visible cleanup

**Step:** Fail raw restoration after cursor and alternate-screen cleanup.

**Expected:** The typed result preserves `command_exit`, reports the exact
restore error, and emits no success message.

### should restore after slash exit

**Step:** Leave the production TUI with slash exit.

**Expected:** The loop reports `command_exit` and completes all cleanup actions.

### should restore after Ctrl-C

**Step:** Leave the production TUI with Ctrl-C.

**Expected:** The loop reports `input_exit` and completes all cleanup actions.

### should restore after Ctrl-D

**Step:** Leave the production TUI with Ctrl-D.

**Expected:** The loop reports `input_exit` and completes all cleanup actions.

### should restore after byte-stream EOF

**Step:** Leave the production TUI when byte input reaches EOF.

**Expected:** The loop reports `input_exit` and completes all cleanup actions.

### should force TUI routing without a tty

**Step:** Request TUI mode while the injected tty probe is false.

**Expected:** `caret_chat` returns TUI mode and enters the production raw loop.

### should force plain routing on a tty

**Step:** Request plain mode while the injected tty probe is true.

**Expected:** `caret_chat` returns plain mode without entering raw mode.

### should automatically route tty input to TUI

**Step:** Select automatic mode with an injected tty.

**Expected:** The tty probe routes to the TUI loop before raw acquisition.

### should automatically route non-tty input to plain mode

**Step:** Select automatic mode without an injected tty.

**Expected:** The tty probe routes to the plain loop and emits its prompt
without raw acquisition.

<details>
<summary>Executable SSpec source</summary>

The complete executable source, including deterministic fake function fields
and every assertion summarized above, is maintained at:

`test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl`

</details>
