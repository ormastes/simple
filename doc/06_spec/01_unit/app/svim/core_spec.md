# svim shared editor core specification

> Validates the foundational shared editor core used by host TUI first and

<!-- sdn-diagram:id=core_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=core_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

core_spec -> std
core_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=core_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# svim shared editor core specification

Validates the foundational shared editor core used by host TUI first and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/svim/core_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the foundational shared editor core used by host TUI first and
future shells later. Covers piece-table storage, anchor updates, modal
commands, registers, splits/tabpages, quickfix flow, and RPC control.

## Scenarios

### svim piece table

#### applies insert and delete edits without flattening the model

1. var table = PieceTable from text
2. table insert
3. expect table to text
4. table delete
5. expect table to text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var table = PieceTable.from_text("abc")
table.insert(1, "XY")
expect table.to_text() to_equal "aXYbc"
table.delete(2, 4)
expect table.to_text() to_equal "aXc"
```

</details>

### svim anchors

#### moves extmark-like anchors across multiline inserts

1. var tracker = AnchorTracker new
2. tracker apply insert


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tracker = AnchorTracker.new()
val id = tracker.create(0, 1, true)
tracker.apply_insert(0, 1, "ZZ\nQ")
val pos = tracker.get(id)
expect pos.row to_equal 1
expect pos.col to_equal 1
```

</details>

#### clamps anchors into deleted ranges

1. var tracker = AnchorTracker new
2. tracker apply delete


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tracker = AnchorTracker.new()
val id = tracker.create(2, 5, true)
tracker.apply_delete(1, 3, 3, 2)
val pos = tracker.get(id)
expect pos.row to_equal 1
expect pos.col to_equal 3
```

</details>

### svim modal editing

#### inserts text in insert mode and tracks cursor

1. var session = SvimSession new
2. session execute named
3. session execute named
4. expect active buffer text
5. expect session current cursor


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
session.execute_named("insert-text", "hello", 1, "")
expect active_buffer_text(session) to_equal "hello"
expect session.current_cursor().col to_equal 5
```

</details>

#### supports line yank delete and put through registers

1. var session = SvimSession new
2. session execute named
3. session execute named
4. session execute named
5. session execute named
6. session execute named
7. session execute named
8. session execute named
9. session execute named
10. expect active buffer text


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
session.execute_named("insert-text", "alpha\nbeta", 1, "")
session.execute_named("set-mode", "normal", 1, "")
session.execute_named("move-up", "", 1, "")
session.execute_named("yank-line", "", 1, "\"")
session.execute_named("move-down", "", 1, "")
session.execute_named("delete-line", "", 1, "")
session.execute_named("put-after", "", 1, "\"")
expect active_buffer_text(session) to_equal "alpha\nalpha\n"
```

</details>

#### supports undo and redo for text edits

1. var session = SvimSession new
2. session execute named
3. session execute named
4. session execute named
5. expect active buffer text
6. session execute named
7. expect active buffer text


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
session.execute_named("insert-text", "abc", 1, "")
session.execute_named("undo", "", 1, "")
expect active_buffer_text(session) to_equal ""
session.execute_named("redo", "", 1, "")
expect active_buffer_text(session) to_equal "abc"
```

</details>

#### supports operator-pending word deletion with counts

1. var session = SvimSession new
2. session execute named
3. session execute named
4. session execute named
5. session execute named
6. session execute
7. expect active buffer text
8. expect session current cursor


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
session.execute_named("insert-text", "alpha beta gamma", 1, "")
session.execute_named("set-mode", "normal", 1, "")
session.execute_named("move-left", "", 16, "")
session.execute(svim_parse_normal_command("2dw"))
expect active_buffer_text(session) to_equal "gamma"
expect session.current_cursor().col to_equal 0
```

</details>

#### supports operator-pending word yank and text objects

1. var session = SvimSession new
2. session execute named
3. session execute named
4. session execute named
5. session execute named
6. session execute
7. session execute named
8. session execute
9. expect active buffer text


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
session.execute_named("insert-text", "alpha beta gamma", 1, "")
session.execute_named("set-mode", "normal", 1, "")
session.execute_named("move-left", "", 16, "")
session.execute(svim_parse_normal_command("2yw"))
expect session.registers.entries[0].content to_equal "alpha beta "
session.execute_named("search-forward", "beta", 1, "")
session.execute(svim_parse_normal_command("diw"))
expect active_buffer_text(session) to_equal "alpha  gamma"
```

</details>

### svim workspace state

#### supports split windows over the same buffer

1. var session = SvimSession new
2. expect session tabs[session current tab index] window ids len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
val result = session.execute_named("split-window", "", 1, "")
expect result.ok to_equal true
expect session.tabs[session.current_tab_index].window_ids.len() to_equal 2
```

</details>

#### supports opening a new tabpage from the current buffer

1. var session = SvimSession new
2. expect session tabs len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
val result = session.execute_named("new-tab", "", 1, "")
expect result.ok to_equal true
expect session.tabs.len() to_equal 2
```

</details>

#### builds quickfix items from diagnostics and jumps to them

1. var session = SvimSession new
2. session replace simple diagnostics
3. expect session quickfix items len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
val buffer_id = session.active_buffer()?.id ?? BufferId(value: 0)
session.replace_simple_diagnostics(buffer_id, [0], [0], ["error"], ["boom"])
expect session.quickfix.items.len() to_equal 1
val jump = session.jump_to_quickfix(0)
expect jump.ok to_equal true
expect jump.message to_equal "boom"
```

</details>

#### cycles quickfix entries through shared commands and commandline aliases

1. var session = SvimSession new
2. session execute named
3. session execute named
4. session execute named
5. session replace simple diagnostics
6. expect session current cursor
7. expect session current cursor
8. expect session current cursor
9. expect session current cursor


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
session.execute_named("insert-text", "line zero\nline one with content", 1, "")
session.execute_named("set-mode", "normal", 1, "")
val buffer_id = session.active_buffer()?.id ?? BufferId(value: 0)
session.replace_simple_diagnostics(buffer_id, [0, 1], [0, 2], ["error", "warn"], ["boom", "bam"])
val next = session.execute_named("quickfix-next", "", 1, "")
expect next.ok to_equal true
expect session.quickfix.selected_index to_equal 1
expect session.current_cursor().row to_equal 1
expect session.current_cursor().col to_equal 2
val prev = session.execute_commandline("cprev")
expect prev.ok to_equal true
expect session.quickfix.selected_index to_equal 0
expect session.current_cursor().row to_equal 0
expect session.current_cursor().col to_equal 0
```

</details>

#### handles rpc snapshot and command requests through the shared session api

1. var session = SvimSession new
2. session execute named


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
val cmd = session.handle_rpc_text("1", "svim.command", "insert-text:rpc")
expect cmd.ok to_equal true
val snap = session.handle_rpc_text("2", "svim.snapshot", "")
expect snap.ok to_equal true
expect snap.result_json to_contain "rpc"
```

</details>

#### moves the cursor for search-forward commands

1. var session = SvimSession new
2. session execute named
3. session execute named
4. session execute named
5. expect session current cursor


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
session.execute_named("insert-text", "alpha beta", 1, "")
session.execute_named("set-mode", "normal", 1, "")
val result = session.execute_named("search-forward", "beta", 1, "")
expect result.ok to_equal true
expect session.current_cursor().col to_equal 6
```

</details>

#### records repeat-search state through the shared command surface

1. var session = SvimSession new
2. session execute named
3. session execute named
4. session execute named
5. session execute commandline
6. expect session current cursor


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
session.execute_named("insert-text", "alpha beta alpha", 1, "")
session.execute_named("set-mode", "normal", 1, "")
session.execute_commandline("search alpha")
expect session.current_cursor().col to_equal 0
expect session.last_search to_equal "alpha"
expect session.last_search_direction to_equal 1
```

</details>

#### tracks visual selection endpoints in the shared session

1. var session = SvimSession new
2. session execute named
3. session execute named
4. session execute named
5. session execute named
6. expect svim snapshot text


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
session.execute_named("insert-text", "hello", 1, "")
session.execute_named("set-mode", "visual", 1, "")
session.execute_named("move-left", "", 2, "")
var selection_end_col = -1
val sel = session.selection
if sel != nil:
    selection_end_col = sel.end.col
expect selection_end_col to_equal 3
expect svim_snapshot_text(session) to_contain "selection"
```

</details>

#### yanks a visual selection into the active register

1. var session = SvimSession new
2. session execute named
3. session execute named
4. session execute named
5. session execute named
6. session execute named


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
session.execute_named("insert-text", "hello", 1, "")
session.execute_named("set-mode", "visual", 1, "")
session.execute_named("move-left", "", 2, "")
session.execute_named("yank-line", "", 1, "\"")
expect session.registers.entries[0].content to_equal "lo"
expect session.mode_state.mode to_equal SvimMode.Normal
```

</details>

#### deletes a visual selection through the shared edit path

1. var session = SvimSession new
2. session execute named
3. session execute named
4. session execute named
5. session execute named
6. session execute named
7. expect active buffer text
8. expect session current cursor


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
session.execute_named("insert-text", "hello", 1, "")
session.execute_named("set-mode", "visual", 1, "")
session.execute_named("move-left", "", 2, "")
session.execute_named("delete-line", "", 1, "\"")
expect active_buffer_text(session) to_equal "hel"
expect session.current_cursor().col to_equal 3
expect session.mode_state.mode to_equal SvimMode.Normal
```

</details>

#### handles forward visual selections with the same yank and delete semantics

1. var session = SvimSession new
2. session execute named
3. session execute named
4. session execute named
5. session execute named
6. session execute named
7. session execute named
8. session execute named
9. session execute named
10. session execute named
11. session execute named
12. expect active buffer text
13. expect session current cursor


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
session.execute_named("insert-text", "hello", 1, "")
session.execute_named("set-mode", "normal", 1, "")
session.execute_named("move-left", "", 5, "")
session.execute_named("set-mode", "visual", 1, "")
session.execute_named("move-right", "", 2, "")
session.execute_named("yank-line", "", 1, "\"")
expect session.registers.entries[0].content to_equal "he"
session.execute_named("set-mode", "visual", 1, "")
session.execute_named("move-right", "", 2, "")
session.execute_named("delete-line", "", 1, "\"")
expect active_buffer_text(session) to_equal "llo"
expect session.current_cursor().col to_equal 0
```

</details>

#### replaces a visual selection with register content on put

1. var session = SvimSession new
2. session execute named
3. session execute named
4. session execute named
5. session execute named
6. session execute named
7. session execute named
8. session execute named
9. session execute named
10. session execute named
11. expect active buffer text
12. expect session current cursor


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
session.execute_named("insert-text", "hello", 1, "")
session.execute_named("set-mode", "visual", 1, "")
session.execute_named("move-left", "", 2, "")
session.execute_named("yank-line", "", 1, "\"")
session.execute_named("move-left", "", 3, "")
session.execute_named("set-mode", "visual", 1, "")
session.execute_named("move-right", "", 2, "")
session.execute_named("put-after", "", 1, "\"")
expect active_buffer_text(session) to_equal "lollo"
expect session.current_cursor().col to_equal 2
expect session.mode_state.mode to_equal SvimMode.Normal
```

</details>

#### supports jump-back after a search move

1. var session = SvimSession new
2. session execute named
3. session execute named
4. session execute named
5. session execute named
6. session execute named
7. expect session current cursor


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
session.execute_named("insert-text", "alpha beta", 1, "")
session.execute_named("set-mode", "normal", 1, "")
session.execute_named("search-forward", "beta", 1, "")
session.execute_named("jump-back", "", 1, "")
expect session.current_cursor().col to_equal 0
```

</details>

#### cycles between buffers through shared commands

1. var session = SvimSession new
2. session focus buffer
3. expect
4. session execute named
5. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var session = SvimSession.new()
val second = session.open_text("/tmp/second.txt", "two")
session.focus_buffer(second)
expect (session.active_buffer()?.path ?? "") to_equal "/tmp/second.txt"
session.execute_named("next-buffer", "", 1, "")
expect (session.active_buffer()?.path ?? "") to_equal ""
```

</details>

#### saves a buffer to disk and reopens it through the shared session

1. var session = SvimSession new
2. session execute named
3. session execute named
4. session execute named
5. expect rt file read text
6. var reopened = SvimSession new
7. expect active buffer text


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/svim_core_spec_save.txt"
val _ = rt_file_delete(path)
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
session.execute_named("insert-text", "saved from spec", 1, "")
session.execute_named("set-mode", "normal", 1, "")
val saved = session.execute_named("save-as", path, 1, "")
expect saved.ok to_equal true
expect rt_file_read_text(path) to_equal "saved from spec"
var reopened = SvimSession.new()
val opened = reopened.open_path(path)
expect opened.ok to_equal true
expect active_buffer_text(reopened) to_equal "saved from spec"
val _cleanup = rt_file_delete(path)
```

</details>

### svim normal command parser

#### parses count-aware motions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = svim_parse_normal_command("3j")
expect cmd.name to_equal "move-down"
expect cmd.count to_equal 3
```

</details>

#### parses shorthand editor commands

1. expect svim parse normal command
2. expect svim parse normal command
3. expect svim parse normal command
4. expect svim parse normal command
5. expect svim parse normal command
6. expect svim parse normal command
7. expect svim parse normal command
8. expect svim parse normal command
9. expect svim parse normal command
10. expect svim parse normal command
11. expect svim parse normal command
12. expect svim parse normal command
13. expect svim parse normal command
14. expect svim parse normal command
15. expect svim parse normal command
16. expect svim parse normal command
17. expect svim parse normal command
18. expect svim parse normal command


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect svim_parse_normal_command("dd").name to_equal "delete-line"
expect svim_parse_normal_command(":w").name to_equal "commandline"
expect svim_parse_normal_command("/term").payload to_equal "term"
expect svim_parse_normal_command("v").payload to_equal "visual"
expect svim_parse_normal_command("bn").name to_equal "next-buffer"
expect svim_parse_normal_command("ctrl-o").name to_equal "jump-back"
expect svim_parse_normal_command("y").name to_equal "yank-line"
expect svim_parse_normal_command("p").name to_equal "put-after"
expect svim_parse_normal_command("]q").name to_equal "quickfix-next"
expect svim_parse_normal_command("[q").name to_equal "quickfix-prev"
expect svim_parse_normal_command("n").name to_equal "search-next"
expect svim_parse_normal_command("N").name to_equal "search-prev"
expect svim_parse_normal_command("2dw").name to_equal "delete-motion"
expect svim_parse_normal_command("2dw").count to_equal 2
expect svim_parse_normal_command("2dw").payload to_equal "word"
expect svim_parse_normal_command("d2w").count to_equal 2
expect svim_parse_normal_command("diw").name to_equal "delete-text-object"
expect svim_parse_normal_command("yaw").payload to_equal "aw"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
