# T32 MCP Server -- Dialog Tool Unit Tests

> Tests for the T32 MCP dialog management layer: dialog item creation, snapshot store/get/remove, change detection between snapshots, and parsing helpers. Also tests connection parsing and item name parsing from the MCP dialog tool handlers. All functions under test are pure (no I/O, no side effects).

<!-- sdn-diagram:id=t32_mcp_dialog_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_mcp_dialog_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_mcp_dialog_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_mcp_dialog_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 MCP Server -- Dialog Tool Unit Tests

Tests for the T32 MCP dialog management layer: dialog item creation, snapshot store/get/remove, change detection between snapshots, and parsing helpers. Also tests connection parsing and item name parsing from the MCP dialog tool handlers. All functions under test are pure (no I/O, no side effects).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #T32-MCP-003 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/app/t32_tools/t32_mcp_dialog_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the T32 MCP dialog management layer: dialog item creation,
snapshot store/get/remove, change detection between snapshots, and
parsing helpers. Also tests connection parsing and item name parsing
from the MCP dialog tool handlers.
All functions under test are pure (no I/O, no side effects).

## Source

`src/lib/nogc_sync_mut/debug/remote/protocol/t32_dialog_manager.spl`
`src/app/mcp/main_lazy_dialog_tools.spl`

## Scenarios

### T32 Dialog Item

#### creation with all fields

#### stores name, kind, value, and exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = T32DialogItem(name: "btn_ok", kind: "button", value: "", exists: true)
expect(item.name).to_equal("btn_ok")
expect(item.kind).to_equal("button")
expect(item.value).to_equal("")
expect(item.exists).to_equal(true)
```

</details>

#### represents a non-existent item

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = T32DialogItem(name: "missing", kind: "unknown", value: "", exists: false)
expect(item.name).to_equal("missing")
expect(item.kind).to_equal("unknown")
expect(item.exists).to_equal(false)
```

</details>

#### stores checkbox kind with boolean value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = T32DialogItem(name: "chk_enable", kind: "checkbox", value: "TRUE()", exists: true)
expect(item.kind).to_equal("checkbox")
expect(item.value).to_equal("TRUE()")
```

</details>

#### stores edit kind with text value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = T32DialogItem(name: "edit_path", kind: "edit", value: "/tmp/test.elf", exists: true)
expect(item.kind).to_equal("edit")
expect(item.value).to_equal("/tmp/test.elf")
```

</details>

### T32 Dialog Snapshot

#### creation

#### stores session_id and practice_state

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "dialog",
    items: [],
    window_names: []
)
expect(snap.session_id).to_equal("s1")
expect(snap.practice_state).to_equal("dialog")
```

</details>

#### stores items list

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item1 = T32DialogItem(name: "btn1", kind: "button", value: "", exists: true)
val item2 = T32DialogItem(name: "edit1", kind: "edit", value: "hello", exists: true)
val snap = T32DialogSnapshot(
    session_id: "s2",
    practice_state: "dialog",
    items: [item1, item2],
    window_names: []
)
expect(snap.items.len()).to_equal(2)
```

</details>

#### stores window_names list

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = T32DialogSnapshot(
    session_id: "s3",
    practice_state: "idle",
    items: [],
    window_names: ["Register.view", "Data.dump"]
)
expect(snap.window_names.len()).to_equal(2)
```

</details>

#### store and get

#### stores and retrieves a snapshot by session_id

1. dialog snapshot store
   - Expected: result.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = T32DialogSnapshot(
    session_id: "test_store_1",
    practice_state: "dialog",
    items: [],
    window_names: []
)
dialog_snapshot_store(snap)
val result = dialog_snapshot_get("test_store_1")
expect(result.?).to_equal(true)
```

</details>

#### returns nil for unknown session_id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = dialog_snapshot_get("nonexistent_session_xyz")
expect(result.?).to_equal(false)
```

</details>

#### overwrites snapshot for same session_id

1. dialog snapshot store
2. dialog snapshot store
   - Expected: result.? is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap1 = T32DialogSnapshot(
    session_id: "test_overwrite_1",
    practice_state: "dialog",
    items: [],
    window_names: []
)
dialog_snapshot_store(snap1)
val snap2 = T32DialogSnapshot(
    session_id: "test_overwrite_1",
    practice_state: "idle",
    items: [],
    window_names: []
)
dialog_snapshot_store(snap2)
val result = dialog_snapshot_get("test_overwrite_1")
expect(result.?).to_equal(true)
```

</details>

#### remove

#### removes a stored snapshot

1. dialog snapshot store
2. dialog snapshot remove
   - Expected: result.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = T32DialogSnapshot(
    session_id: "test_remove_1",
    practice_state: "dialog",
    items: [],
    window_names: []
)
dialog_snapshot_store(snap)
dialog_snapshot_remove("test_remove_1")
val result = dialog_snapshot_get("test_remove_1")
expect(result.?).to_equal(false)
```

</details>

#### no-ops when removing nonexistent session

1. dialog snapshot remove
   - Expected: result.? is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dialog_snapshot_remove("nonexistent_remove_xyz")
# Should not error — just a no-op
val result = dialog_snapshot_get("nonexistent_remove_xyz")
expect(result.?).to_equal(false)
```

</details>

### T32 Dialog Change Detection

#### dialog opened

#### detects transition from idle to dialog

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "idle",
    items: [],
    window_names: []
)
val new_snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "dialog",
    items: [],
    window_names: []
)
val changes = dialog_compute_changes(old_snap, new_snap)
expect(changes.len()).to_equal(1)
expect(changes[0].change_type).to_equal("dialog_opened")
expect(changes[0].window_name).to_equal("practice_dialog")
expect(changes[0].old_value).to_equal("idle")
expect(changes[0].new_value).to_equal("dialog")
```

</details>

#### dialog closed

#### detects transition from dialog to idle

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "dialog",
    items: [],
    window_names: []
)
val new_snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "idle",
    items: [],
    window_names: []
)
val changes = dialog_compute_changes(old_snap, new_snap)
expect(changes.len()).to_equal(1)
expect(changes[0].change_type).to_equal("dialog_closed")
expect(changes[0].old_value).to_equal("dialog")
expect(changes[0].new_value).to_equal("idle")
```

</details>

#### item changed

#### detects value change in a dialog item

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_item = T32DialogItem(name: "edit_path", kind: "edit", value: "/old/path", exists: true)
val new_item = T32DialogItem(name: "edit_path", kind: "edit", value: "/new/path", exists: true)
val old_snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "dialog",
    items: [old_item],
    window_names: []
)
val new_snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "dialog",
    items: [new_item],
    window_names: []
)
val changes = dialog_compute_changes(old_snap, new_snap)
expect(changes.len()).to_equal(1)
expect(changes[0].change_type).to_equal("item_changed")
expect(changes[0].item_name).to_equal("edit_path")
expect(changes[0].old_value).to_equal("/old/path")
expect(changes[0].new_value).to_equal("/new/path")
```

</details>

#### item added

#### detects a newly appeared item

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val new_item = T32DialogItem(name: "btn_new", kind: "button", value: "", exists: true)
val old_snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "dialog",
    items: [],
    window_names: []
)
val new_snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "dialog",
    items: [new_item],
    window_names: []
)
val changes = dialog_compute_changes(old_snap, new_snap)
expect(changes.len()).to_equal(1)
expect(changes[0].change_type).to_equal("item_added")
expect(changes[0].item_name).to_equal("btn_new")
expect(changes[0].new_value).to_equal("")
```

</details>

#### item removed

#### detects a removed item

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_item = T32DialogItem(name: "btn_gone", kind: "button", value: "click", exists: true)
val old_snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "dialog",
    items: [old_item],
    window_names: []
)
val new_snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "dialog",
    items: [],
    window_names: []
)
val changes = dialog_compute_changes(old_snap, new_snap)
expect(changes.len()).to_equal(1)
expect(changes[0].change_type).to_equal("item_removed")
expect(changes[0].item_name).to_equal("btn_gone")
expect(changes[0].old_value).to_equal("click")
```

</details>

#### window opened

#### detects a newly opened window

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "idle",
    items: [],
    window_names: []
)
val new_snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "idle",
    items: [],
    window_names: ["Register.view"]
)
val changes = dialog_compute_changes(old_snap, new_snap)
expect(changes.len()).to_equal(1)
expect(changes[0].change_type).to_equal("window_opened")
expect(changes[0].window_name).to_equal("Register.view")
```

</details>

#### window closed

#### detects a closed window

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "idle",
    items: [],
    window_names: ["Data.dump"]
)
val new_snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "idle",
    items: [],
    window_names: []
)
val changes = dialog_compute_changes(old_snap, new_snap)
expect(changes.len()).to_equal(1)
expect(changes[0].change_type).to_equal("window_closed")
expect(changes[0].window_name).to_equal("Data.dump")
```

</details>

#### no changes

#### returns empty list when snapshots are identical

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val item = T32DialogItem(name: "edit1", kind: "edit", value: "hello", exists: true)
val old_snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "dialog",
    items: [item],
    window_names: ["Register.view"]
)
val new_snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "dialog",
    items: [item],
    window_names: ["Register.view"]
)
val changes = dialog_compute_changes(old_snap, new_snap)
expect(changes.len()).to_equal(0)
```

</details>

#### multiple changes

#### detects multiple item changes at once

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val old_a = T32DialogItem(name: "field_a", kind: "edit", value: "old_a", exists: true)
val old_b = T32DialogItem(name: "field_b", kind: "edit", value: "old_b", exists: true)
val old_c = T32DialogItem(name: "field_c", kind: "checkbox", value: "FALSE", exists: true)
val new_a = T32DialogItem(name: "field_a", kind: "edit", value: "new_a", exists: true)
val new_b = T32DialogItem(name: "field_b", kind: "edit", value: "old_b", exists: true)
val new_d = T32DialogItem(name: "field_d", kind: "button", value: "", exists: true)
val old_snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "dialog",
    items: [old_a, old_b, old_c],
    window_names: []
)
val new_snap = T32DialogSnapshot(
    session_id: "s1",
    practice_state: "dialog",
    items: [new_a, new_b, new_d],
    window_names: []
)
val changes = dialog_compute_changes(old_snap, new_snap)
# field_a changed, field_c removed, field_d added = 3 changes
expect(changes.len()).to_equal(3)
```

</details>

### T32 Dialog Parse Collected

#### basic parsing

#### parses name=value entries into DialogItems

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = ["btn_ok=OK", "edit_path=/tmp/test.elf"]
val items = dialog_parse_collected(entries)
expect(items.len()).to_equal(2)
expect(items[0].name).to_equal("btn_ok")
expect(items[0].value).to_equal("OK")
expect(items[0].exists).to_equal(true)
expect(items[1].name).to_equal("edit_path")
expect(items[1].value).to_equal("/tmp/test.elf")
```

</details>

#### handles =<not found> as non-existent

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = ["missing_item=<not found>"]
val items = dialog_parse_collected(entries)
expect(items.len()).to_equal(1)
expect(items[0].name).to_equal("missing_item")
expect(items[0].exists).to_equal(false)
expect(items[0].kind).to_equal("unknown")
```

</details>

#### returns empty list for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries: [text] = []
val items = dialog_parse_collected(entries)
expect(items.len()).to_equal(0)
```

</details>

#### checkbox detection

#### detects TRUE() as checkbox kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = ["chk_enable=TRUE()"]
val items = dialog_parse_collected(entries)
expect(items.len()).to_equal(1)
expect(items[0].kind).to_equal("checkbox")
```

</details>

#### detects FALSE as checkbox kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = ["chk_disable=FALSE"]
val items = dialog_parse_collected(entries)
expect(items.len()).to_equal(1)
expect(items[0].kind).to_equal("checkbox")
```

</details>

#### detects regular text as edit kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = ["field1=some text"]
val items = dialog_parse_collected(entries)
expect(items.len()).to_equal(1)
expect(items[0].kind).to_equal("edit")
```

</details>

#### values containing equals sign

#### preserves value with embedded equals

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = ["expr=x=y=z"]
val items = dialog_parse_collected(entries)
expect(items.len()).to_equal(1)
expect(items[0].name).to_equal("expr")
expect(items[0].value).to_equal("x=y=z")
```

</details>

### T32 Dialog Empty Snapshot

#### creation

#### creates snapshot with given session_id and state

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = dialog_empty_snapshot("sess_1", "idle")
expect(snap.session_id).to_equal("sess_1")
expect(snap.practice_state).to_equal("idle")
expect(snap.items.len()).to_equal(0)
expect(snap.window_names.len()).to_equal(0)
```

</details>

#### creates snapshot with dialog state

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val snap = dialog_empty_snapshot("sess_2", "dialog")
expect(snap.practice_state).to_equal("dialog")
expect(snap.items.len()).to_equal(0)
```

</details>

### T32 Connection Parsing

#### host:port format

#### parses localhost:20000

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (host, port) = test_parse_connection("localhost:20000")
expect(host).to_equal("localhost")
expect(port).to_equal("20000")
```

</details>

#### parses custom host and port

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (host, port) = test_parse_connection("192.168.1.5:21000")
expect(host).to_equal("192.168.1.5")
expect(port).to_equal("21000")
```

</details>

#### t32:// URI format

#### strips t32:// prefix and parses host:port

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (host, port) = test_parse_connection("t32://192.168.1.5:21000")
expect(host).to_equal("192.168.1.5")
expect(port).to_equal("21000")
```

</details>

#### strips t32:// prefix with localhost

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (host, port) = test_parse_connection("t32://localhost:20000")
expect(host).to_equal("localhost")
expect(port).to_equal("20000")
```

</details>

#### bare hostname

#### defaults port to 20000 for bare hostname

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (host, port) = test_parse_connection("myhost")
expect(host).to_equal("myhost")
expect(port).to_equal("20000")
```

</details>

#### empty string

#### defaults to localhost:20000 for empty input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (host, port) = test_parse_connection("")
expect(host).to_equal("localhost")
expect(port).to_equal("20000")
```

</details>

### T32 Item Name Parsing

#### comma-separated names

#### parses three comma-separated names

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = test_parse_item_names("btn1,field2,check3")
expect(names.len()).to_equal(3)
expect(names[0]).to_equal("btn1")
expect(names[1]).to_equal("field2")
expect(names[2]).to_equal("check3")
```

</details>

#### empty input

#### returns empty list for empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = test_parse_item_names("")
expect(names.len()).to_equal(0)
```

</details>

#### whitespace trimming

#### trims whitespace around names

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = test_parse_item_names(" btn1 , field2 ")
expect(names.len()).to_equal(2)
expect(names[0]).to_equal("btn1")
expect(names[1]).to_equal("field2")
```

</details>

#### single item

#### parses a single name without commas

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = test_parse_item_names("only_one")
expect(names.len()).to_equal(1)
expect(names[0]).to_equal("only_one")
```

</details>

#### trailing comma

#### ignores empty segments from trailing comma

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = test_parse_item_names("a,b,")
expect(names.len()).to_equal(2)
expect(names[0]).to_equal("a")
expect(names[1]).to_equal("b")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
