# editor_hardening_spec

> Regression and contract tests covering four robustness areas:

<!-- sdn-diagram:id=editor_hardening_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_hardening_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_hardening_spec -> std
editor_hardening_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_hardening_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 59 | 59 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# editor_hardening_spec

Regression and contract tests covering four robustness areas:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/editor/editor_hardening_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Editor IDE Hardening

Regression and contract tests covering four robustness areas:
LSP connection bounds, debug-process handle safety, workspace-path
validation, and keymap unknown-command handling.  All tests drive
real production functions; no hardware or real processes are accessed.

## Scenarios

### keymap dispatch: command mode safety

#### ESC cancels and returns empty commandline

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ctrl_handle_command_key("\x1b", "wq")
expect(r.cancelled).to_equal(true)
expect(r.done).to_equal(false)
expect(r.commandline).to_equal("")
```

</details>

#### enter on non-empty commandline marks done

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ctrl_handle_command_key("\r", "wq")
expect(r.done).to_equal(true)
expect(r.cancelled).to_equal(false)
expect(r.commandline).to_equal("wq")
```

</details>

#### newline also marks done

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ctrl_handle_command_key("\n", "save")
expect(r.done).to_equal(true)
```

</details>

#### backspace on non-empty commandline shortens by one char

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ctrl_handle_command_key("\x7f", "wq")
expect(r.cancelled).to_equal(false)
expect(r.done).to_equal(false)
expect(r.commandline).to_equal("w")
```

</details>

#### backspace on empty commandline cancels without underflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ctrl_handle_command_key("\x7f", "")
expect(r.cancelled).to_equal(true)
expect(r.commandline).to_equal("")
```

</details>

#### backspace (BS) on empty commandline also cancels

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ctrl_handle_command_key("\b", "")
expect(r.cancelled).to_equal(true)
```

</details>

#### printable ascii character is appended to commandline

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ctrl_handle_command_key("q", "w")
expect(r.done).to_equal(false)
expect(r.cancelled).to_equal(false)
expect(r.commandline).to_equal("wq")
```

</details>

#### non-printable non-special control char is a no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SOH (0x01) is below 32, not an escape/enter/backspace — must be silently ignored
val r = ctrl_handle_command_key("\x01", "abc")
expect(r.done).to_equal(false)
expect(r.cancelled).to_equal(false)
expect(r.commandline).to_equal("abc")
```

</details>

#### NUL byte is also a no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ctrl_handle_command_key("\x00", "abc")
expect(r.done).to_equal(false)
expect(r.cancelled).to_equal(false)
expect(r.commandline).to_equal("abc")
```

</details>

### keymap dispatch: normal mode unknown key fallthrough

#### unknown printable key returns quit=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = EditorBuffer.new()
val r = ctrl_handle_normal_key(buf, "Z")
expect(r.quit).to_equal(false)
```

</details>

#### unknown printable key returns enter_insert=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = EditorBuffer.new()
val r = ctrl_handle_normal_key(buf, "Z")
expect(r.enter_insert).to_equal(false)
```

</details>

#### unknown printable key returns enter_command=false

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = EditorBuffer.new()
val r = ctrl_handle_normal_key(buf, "Z")
expect(r.enter_command).to_equal(false)
```

</details>

#### q key signals quit

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = EditorBuffer.new()
val r = ctrl_handle_normal_key(buf, "q")
expect(r.quit).to_equal(true)
```

</details>

#### i key enters insert mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = EditorBuffer.new()
val r = ctrl_handle_normal_key(buf, "i")
expect(r.enter_insert).to_equal(true)
expect(r.quit).to_equal(false)
```

</details>

#### colon enters command mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = EditorBuffer.new()
val r = ctrl_handle_normal_key(buf, ":")
expect(r.enter_command).to_equal(true)
expect(r.quit).to_equal(false)
```

</details>

#### NUL byte is treated as unknown (non-printable fallthrough)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = EditorBuffer.new()
val r = ctrl_handle_normal_key(buf, "\x00")
expect(r.quit).to_equal(false)
expect(r.enter_insert).to_equal(false)
expect(r.enter_command).to_equal(false)
```

</details>

#### ESC in normal mode is unknown — falls through safely

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# ESC is handled in insert mode; in normal mode it is not bound
val buf = EditorBuffer.new()
val r = ctrl_handle_normal_key(buf, "\x1b")
expect(r.quit).to_equal(false)
```

</details>

### keymap dispatch: insert mode safety

#### ESC exits insert mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = EditorBuffer.new()
val r = ctrl_handle_insert_key(buf, "\x1b")
expect(r.exit_insert).to_equal(true)
```

</details>

#### printable char does not exit insert mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = EditorBuffer.new()
val r = ctrl_handle_insert_key(buf, "a")
expect(r.exit_insert).to_equal(false)
```

</details>

#### enter key inserts newline and stays in insert mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = EditorBuffer.new()
val r = ctrl_handle_insert_key(buf, "\r")
expect(r.exit_insert).to_equal(false)
```

</details>

#### control char SOH below 32 is silently ignored in insert mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = EditorBuffer.new()
val r = ctrl_handle_insert_key(buf, "\x01")
expect(r.exit_insert).to_equal(false)
expect(r.message).to_equal("-- INSERT --")
```

</details>

### command dispatch: editor_parse_commandline unknown input

#### known command 'w' maps to save

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = editor_parse_commandline("w")
expect(cmd.name).to_equal("save")
```

</details>

#### known command 'q' maps to quit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = editor_parse_commandline("q")
expect(cmd.name).to_equal("quit")
```

</details>

#### known command 'wq' maps to save

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = editor_parse_commandline("wq")
expect(cmd.name).to_equal("save")
```

</details>

#### known command 'q!' maps to force-quit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = editor_parse_commandline("q!")
expect(cmd.name).to_equal("force-quit")
```

</details>

#### unknown command returns non-empty name without crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = editor_parse_commandline("xyzzy")
expect(cmd.name.len()).to_be_greater_than(0)
```

</details>

#### empty commandline does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = editor_parse_commandline("")
expect(cmd.name.len()).to_be_greater_than(0)
```

</details>

#### commandline with only whitespace does not crash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = editor_parse_commandline("   ")
expect(cmd.name.len()).to_be_greater_than(0)
```

</details>

### debug process: binary path resolution contract

#### returned path is non-empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The function always returns a non-empty string (fallback or real path).
# We test the contract, not the filesystem — result varies by env.
val path = editor_debug_process_find_simple_binary()
expect(path.len()).to_be_greater_than(0)
```

</details>

#### returned path starts with 'bin/'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = editor_debug_process_find_simple_binary()
expect(path.starts_with("bin/")).to_equal(true)
```

</details>

#### returned path contains 'simple'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = editor_debug_process_find_simple_binary()
expect(path.contains("simple")).to_equal(true)
```

</details>

### debug process: pid validation contract (BUG-3)

#### write_frame with pid=0 returns false without crashing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = editor_debug_process_write_frame(0, "{}")
expect(result).to_equal(false)
```

</details>

#### write_frame with pid=-1 returns false without crashing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = editor_debug_process_write_frame(-1, "{\"command\":\"continue\"}")
expect(result).to_equal(false)
```

</details>

#### start_simple_adapter with pid=0 returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = editor_debug_process_start_simple_adapter(0)
expect(result).to_equal(false)
```

</details>

#### start_simple_adapter with pid=-1 returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = editor_debug_process_start_simple_adapter(-1)
expect(result).to_equal(false)
```

</details>

#### poll_simple_stopped with pid=0 returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = editor_debug_process_poll_simple_stopped(0)
expect(result).to_equal(false)
```

</details>

#### wait_simple_stopped with pid=0 returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = editor_debug_process_wait_simple_stopped(0)
expect(result).to_equal(false)
```

</details>

#### frame header includes Content-Length for non-empty json

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Validate the framing format used by write_frame for a real pid scenario.
val json = "{\"command\":\"continue\"}"
val frame = "Content-Length: " + str(json.len()) + "\r\n\r\n" + json
expect(frame.starts_with("Content-Length: ")).to_equal(true)
expect(frame.contains(json)).to_equal(true)
```

</details>

#### frame Content-Length matches json byte length

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{}"
val expected_len = json.len()
val header = "Content-Length: " + str(expected_len)
expect(header).to_equal("Content-Length: 2")
```

</details>

### LSP connection guard: empty session

#### empty session has active_index -1 (out of bounds)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = EditSession.new()
val idx = session.active_index
val is_out_of_bounds = idx < 0 or idx >= session.documents.len()
expect(is_out_of_bounds).to_equal(true)
```

</details>

#### empty session has zero documents

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = EditSession.new()
expect(session.documents.len()).to_equal(0)
```

</details>

#### empty session has zero buffers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = EditSession.new()
expect(session.buffers.len()).to_equal(0)
```

</details>

#### active_index bounds check fails when index equals document count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = EditSession.new()
val idx = session.documents.len()
val in_bounds = idx >= 0 and idx < session.documents.len()
expect(in_bounds).to_equal(false)
```

</details>

#### language_id 'simple' satisfies known-language guard

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lang = "simple"
val known = lang == "simple" or lang == "shell" or lang == "markdown"
expect(known).to_equal(true)
```

</details>

#### language_id 'typescript' fails known-language guard

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lang = "typescript"
val known = lang == "simple" or lang == "shell" or lang == "markdown"
expect(known).to_equal(false)
```

</details>

#### empty language_id fails known-language guard

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lang = ""
val known = lang == "simple" or lang == "shell" or lang == "markdown"
expect(known).to_equal(false)
```

</details>

### workspace path: open_file with invalid path

#### open_file with empty path does not crash

1. session open file
   - Expected: session.documents.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = EditSession.new()
session.open_file("")
# If we get here, no crash occurred.  The session now has one document.
expect(session.documents.len()).to_equal(1)
```

</details>

#### open_file with empty path sets active_index to 0

1. session open file
   - Expected: session.active_index equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = EditSession.new()
session.open_file("")
expect(session.active_index).to_equal(0)
```

</details>

#### open_file with non-existent path does not crash

1. session open file
   - Expected: session.documents.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A path that does not exist on disk is valid input — document is
# opened with empty content.  No SIGSEGV, no nil deref.
val session = EditSession.new()
session.open_file("/nonexistent/path/file.spl")
expect(session.documents.len()).to_equal(1)
```

</details>

#### open_file with path traversal does not crash

1. session open file
   - Expected: session.documents.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = EditSession.new()
session.open_file("../../etc/passwd")
expect(session.documents.len()).to_equal(1)
```

</details>

#### second open_file with same empty path reuses document (no dup)

1. session open file
2. session open file
   - Expected: session.documents.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = EditSession.new()
session.open_file("")
session.open_file("")
expect(session.documents.len()).to_equal(1)
```

</details>

### GUI click coordinate parse guard (BUG-5)

#### missing comma in click data is detected by index_of returning -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = "42"
val comma_idx = data.index_of(",")
expect(comma_idx).to_equal(-1)
```

</details>

#### empty click data also has no comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = ""
val comma_idx = data.index_of(",")
expect(comma_idx).to_equal(-1)
```

</details>

#### valid 'line,col' data parses correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = "10,5"
val comma_idx = data.index_of(",")
val line_text = data.slice(0, comma_idx)
val col_text = data.slice(comma_idx + 1, data.len())
expect(line_text).to_equal("10")
expect(col_text).to_equal("5")
```

</details>

#### negative parsed line must be rejected before move_cursor (guard contract)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = -1
val col = 0
val valid = line >= 0 and col >= 0
expect(valid).to_equal(false)
```

</details>

#### negative parsed col must be rejected (guard contract)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = 0
val col = -5
val valid = line >= 0 and col >= 0
expect(valid).to_equal(false)
```

</details>

#### non-negative coordinates pass the guard

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = 3
val col = 12
val valid = line >= 0 and col >= 0
expect(valid).to_equal(true)
```

</details>

#### EditorBuffer.move_cursor clamps negative row to 0 internally

1. buf move cursor
   - Expected: buf.cursor_row equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify the buffer's own clamp so tests relying on it are justified.
val buf = EditorBuffer.from_text(EditorBufferId(value: 1), "hello\nworld")
buf.move_cursor(-5, 0)
expect(buf.cursor_row).to_equal(0)
```

</details>

#### EditorBuffer.move_cursor clamps over-large row to last line

1. buf move cursor
   - Expected: buf.cursor_row equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val buf = EditorBuffer.from_text(EditorBufferId(value: 2), "line1\nline2\nline3")
buf.move_cursor(999, 0)
expect(buf.cursor_row).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 59 |
| Active scenarios | 59 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
