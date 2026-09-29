# svim shared editor core specification

> Validates the foundational shared editor core used by host TUI first and

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
| Source | `test/unit/app/svim/core_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Validates the foundational shared editor core used by host TUI first and
future shells later. Covers piece-table storage, anchor updates, modal
commands, registers, splits/tabpages, quickfix flow, and RPC control.

## Scenarios

### svim piece table

#### applies insert and delete edits without flattening the model

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- applies insert and delete edits without flattening the model


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies insert and delete edits without flattening the model")
var table = PieceTable.from_text("abc")
table.insert(1, "XY")
expect table.to_text() to_equal "aXYbc"
table.delete(2, 4)
expect table.to_text() to_equal "aXc"
```

</details>

### svim anchors

#### moves extmark-like anchors across multiline inserts

- moves extmark-like anchors across multiline inserts


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("moves extmark-like anchors across multiline inserts")
var tracker = AnchorTracker.new()
val id = tracker.create(0, 1, true)
tracker.apply_insert(0, 1, "ZZ\nQ")
val pos = tracker.get(id)
expect pos.row to_equal 1
expect pos.col to_equal 1
```

</details>

#### clamps anchors into deleted ranges

- clamps anchors into deleted ranges


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clamps anchors into deleted ranges")
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

- inserts text in insert mode and tracks cursor


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("inserts text in insert mode and tracks cursor")
var session = SvimSession.new()
session.execute_named("set-mode", "insert", 1, "")
session.execute_named("insert-text", "hello", 1, "")
expect active_buffer_text(session) to_equal "hello"
expect session.current_cursor().col to_equal 5
```

</details>

#### supports line yank delete and put through registers

- supports line yank delete and put through registers


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports line yank delete and put through registers")
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

- supports undo and redo for text edits


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports undo and redo for text edits")
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

- supports operator-pending word deletion with counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports operator-pending word deletion with counts")
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

- supports operator-pending word yank and text objects


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports operator-pending word yank and text objects")
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

- supports split windows over the same buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports split windows over the same buffer")
var session = SvimSession.new()
val result = session.execute_named("split-window", "", 1, "")
expect result.ok to_equal true
expect session.tabs[session.current_tab_index].window_ids.len() to_equal 2
```

</details>

#### supports opening a new tabpage from the current buffer

- supports opening a new tabpage from the current buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports opening a new tabpage from the current buffer")
var session = SvimSession.new()
val result = session.execute_named("new-tab", "", 1, "")
expect result.ok to_equal true
expect session.tabs.len() to_equal 2
```

</details>

#### builds quickfix items from diagnostics and jumps to them

- builds quickfix items from diagnostics and jumps to them


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds quickfix items from diagnostics and jumps to them")
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

- cycles quickfix entries through shared commands and commandline aliases


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cycles quickfix entries through shared commands and commandline aliases")
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

- handles rpc snapshot and command requests through the shared session api


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles rpc snapshot and command requests through the shared session api")
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

- moves the cursor for search-forward commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("moves the cursor for search-forward commands")
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

- records repeat-search state through the shared command surface


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("records repeat-search state through the shared command surface")
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

- tracks visual selection endpoints in the shared session


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tracks visual selection endpoints in the shared session")
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

- yanks a visual selection into the active register


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("yanks a visual selection into the active register")
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

- deletes a visual selection through the shared edit path


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("deletes a visual selection through the shared edit path")
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

- handles forward visual selections with the same yank and delete semantics


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles forward visual selections with the same yank and delete semantics")
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

- replaces a visual selection with register content on put


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces a visual selection with register content on put")
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

- supports jump-back after a search move


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports jump-back after a search move")
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

- cycles between buffers through shared commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cycles between buffers through shared commands")
var session = SvimSession.new()
val second = session.open_text("/tmp/second.txt", "two")
session.focus_buffer(second)
expect (session.active_buffer()?.path ?? "") to_equal "/tmp/second.txt"
session.execute_named("next-buffer", "", 1, "")
expect (session.active_buffer()?.path ?? "") to_equal ""
```

</details>

#### saves a buffer to disk and reopens it through the shared session

- saves a buffer to disk and reopens it through the shared session


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("saves a buffer to disk and reopens it through the shared session")
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

- parses count-aware motions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses count-aware motions")
val cmd = svim_parse_normal_command("3j")
expect cmd.name to_equal "move-down"
expect cmd.count to_equal 3
```

</details>

#### parses shorthand editor commands

- parses shorthand editor commands


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses shorthand editor commands")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e34aa8a7bd5c8583dc5faba56b9237d436fa331be58ad956f4ec4bfcc82f4fff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e34aa8a7bd5c8583dc5faba56b9237d436fa331be58ad956f4ec4bfcc82f4fff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e34aa8a7bd5c8583dc5faba56b9237d436fa331be58ad956f4ec4bfcc82f4fff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/svim/core_spec.spl
mirror: doc/06_spec/unit/app/svim/core_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/svim/core_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/svim/core_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/svim/core_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies insert and delete edits without flattening the model' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/svim/core_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'moves extmark-like anchors across multiline inserts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/svim/core_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clamps anchors into deleted ranges' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
