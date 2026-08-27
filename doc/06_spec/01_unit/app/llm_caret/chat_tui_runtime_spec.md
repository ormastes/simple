# LLM Caret TUI Runtime Seam Unit Spec

> Source-synchronized manual for deterministic direct-production coverage of
> `CaretIo`, `_draw_frame`, `_read_line`, `run_chat_tui`,
> `run_chat_plain`, and `caret_chat`. The fake I/O uses function fields only:
> it does not copy production algorithms, open a terminal, or declare runtime
> externs. Live PTY, panic, and signal evidence remain outside this unit scope.

| Tests | Active | Skipped | Pending | Executed |
|------:|-------:|--------:|--------:|---------:|
| 20 | 20 | 0 | 0 | 0 |

**Provenance warning:** This manual is source-synchronized only. Its scenarios
have not been executed by a provenance-qualified self-hosted runtime, so the
zero executed count is not a passing result.

**Executable source:** `test/01_unit/app/llm_caret/chat_tui_runtime_spec.spl`

The promptless-command fixture uses the frozen
`CaretPromptlessCommandCase(input, canonical, expected_message)` record.
`setup_promptless_command_cases` supplies `/compact`, `/summarize`, `/init`,
and `/bootstrap`; `check_promptless_dispatch` checks their exact canonical
messages plus the injected plain-loop result, counters, input consumption, and
I/O event trace.

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

### should keep every draw within undersized terminal rows

**Step:** Configure a terminal below the minimum layout height

**Step:** Draw one bounded frame through deterministic CaretIo

**Step:** Check every draw row stays inside the terminal snapshot

**Expected:** A five-row terminal is queried once, every captured draw row is
non-negative and less than five, and the bounded frame flushes exactly once.

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

### should ignore blank plain input without discarding later commands

**Step:** Queue blank input before a valid plain turn

**Step:** Run the production plain loop through deterministic CaretIo

**Step:** Check blank input was ignored and the later turn persisted

**Expected:** Empty and whitespace-only lines do not end the loop or reach the
model. The later `hello` turn is submitted exactly once, persisted as two
messages in `fixture-session`, visibly answered, and followed by `/exit` with
`command_exit`; all four lines are consumed without raw-terminal mutation.

### should process plain model commands and persist model turns

**Step:** Switch model, submit one turn, and exit the production plain loop.

**Expected:** The model hook observes `sonnet`, one complete conversation is
persisted to the current session, and the visible model/assistant output is
emitted. The responder counter is exactly one, providing the positive control
for the following promptless-command scenario's zero-call assertion.

### should dispatch accepted promptless aliases without model submission

**Step:** Load the accepted promptless command aliases.

**Expected:** The fixture loads `/compact` and `/init` plus the aliases
`/summarize` → `/compact` and `/bootstrap` → `/init`, with exact canonical
unimplemented messages.

**Step:** Dispatch the command through the shipped Caret path.

**Expected:** Injected `CaretIo` feeds `/compact`, `/summarize`, `/init`,
`/bootstrap`, and `/exit` through `run_chat_plain`.

**Step:** Check canonical output and zero model submission.

**Expected:** The result is `mode=plain`, `ok=true`, and
`exit_reason=command_exit`. The complete output is exactly:

```text
"> Command not implemented in Caret: /compact\n> Command not implemented in Caret: /compact\n> Command not implemented in Caret: /init\n> Command not implemented in Caret: /init\n> "
```

All five lines are consumed. The responder and persistence counters stay zero;
the byte, geometry, draw, and flush counters stay zero; and the I/O trace
contains only the nine expected emits, proving no raw-mode, alternate-screen,
or cursor mutation. This is injected component evidence only, not cached
process or installed-wrapper evidence.

## REQ-LLM-CARET-HIDDEN-008: plain hidden-command admission

### should conceal hidden canonical and alias commands and reject disabled aliases

**Step:** Queue `/debug-tool-call`, `/debug_tool_call`, `/remote_setup`, and
`/exit` with the hidden gate disabled.

**Step:** Dispatch the production plain loop through injected `CaretIo`.

**Step:** Check concealed and disabled output has no side effects.

**Expected:** Both hidden spellings are reported as unknown and never reach the
hidden hook; disabled `/remote_setup` reports its disabled result. The responder
and persistence hooks remain unused, and plain-mode processing makes no
`begin_tui` or `end_tui` call. This is deterministic component evidence for
non-TTY routing, not cached-wrapper process evidence.

## REQ-LLM-CARET-TUI-HARDEN-007: lifecycle and routing

### should compensate setup failures without drawing model calls or persistence

**Step:** Make the typed `begin_tui` boundary fail in each setup phase:
`raw-mode`, `alternate-screen`, and `cursor-hide`.

**Expected:** `run_chat_tui` returns TUI mode with
`exit_reason=terminal-setup-failed`, preserves the boundary error, invokes
`begin_tui` once and compensating `end_tui` once, and performs no drawing,
output, model call, or persistence.

### should end the TUI exactly once and emit the success footer

**Step:** Exit the production TUI through `/exit` after successful typed setup.

**Expected:** The result is a successful `command_exit`; `begin_tui` and
`end_tui` each run exactly once, the event trace starts with `begin_tui` and
ends with `end_tui|emit|`, and the footer is `chat session ended\n`.

### should report cleanup failure without a success footer

**Step:** Make the typed `end_tui` cleanup boundary fail after `/exit`.

**Expected:** The result is unsuccessful with
`exit_reason=terminal-cleanup-failed`, preserves the cleanup error, calls both
lifecycle boundaries once, and emits no success footer.

### should end exactly once for command control and EOF exits

**Step:** Exercise `/exit`, Ctrl-C, Ctrl-D, and byte-stream EOF through the
production TUI loop.

**Expected:** Each normal exit completes with exactly one `begin_tui` and one
`end_tui` call, and emits `chat session ended\n`. The shared typed lifecycle,
not primitive raw/alternate-screen/cursor callbacks, owns setup and cleanup.

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
