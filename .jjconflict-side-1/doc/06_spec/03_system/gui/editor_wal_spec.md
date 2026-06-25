# Editor Wal Specification

> <details>

<!-- sdn-diagram:id=editor_wal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_wal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_wal_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_wal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Wal Specification

## Scenarios

### editor WAL — entry format

#### defines WalEntry with sequence, table, operation, key, data_sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("struct WalEntry:")).to_equal(true)
expect(src.contains("sequence: i64")).to_equal(true)
expect(src.contains("table: text")).to_equal(true)
expect(src.contains("operation: text")).to_equal(true)
expect(src.contains("key: text")).to_equal(true)
expect(src.contains("data_sdn: text")).to_equal(true)
```

</details>

#### defines WalWriter with wal_path and checkpoint_threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("class WalWriter:")).to_equal(true)
expect(src.contains("wal_path: text")).to_equal(true)
expect(src.contains("checkpoint_threshold: i64")).to_equal(true)
```

</details>

#### has append, append_set, append_delete methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("me append(table: text, operation: text, key: text, data_sdn: text) -> bool")).to_equal(true)
expect(src.contains("me append_set(table: text, key: text, data_sdn: text) -> bool")).to_equal(true)
expect(src.contains("me append_delete(table: text, key: text) -> bool")).to_equal(true)
```

</details>

#### uses WAL| prefix format for entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("WAL|")).to_equal(true)
```

</details>

### editor WAL — checkpoint

#### has checkpoint method

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("me checkpoint() -> bool")).to_equal(true)
```

</details>

#### writes to temp file then renames for atomicity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("me.db_path + \".tmp\"")).to_equal(true)
```

</details>

#### clears WAL after successful checkpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("me.entry_count = 0")).to_equal(true)
```

</details>

#### auto-checkpoints at threshold

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("me.entry_count >= me.checkpoint_threshold")).to_equal(true)
expect(src.contains("me.checkpoint()")).to_equal(true)
```

</details>

### editor WAL — replay

#### defines WalReader class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("class WalReader:")).to_equal(true)
```

</details>

#### has read_entries and has_entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("fn read_entries() -> [WalEntry]")).to_equal(true)
expect(src.contains("fn has_entries() -> bool")).to_equal(true)
```

</details>

#### parses WAL entries from content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("fn wal_parse_entries(content: text) -> [WalEntry]")).to_equal(true)
```

</details>

#### applies entries to merge with existing DB

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("fn _wal_apply_entries(db_content: text, entries: [WalEntry]) -> text")).to_equal(true)
```

</details>

### editor session DB — persistence

#### defines SessionDb class

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session_db.spl")
expect(src.contains("class SessionDb:")).to_equal(true)
expect(src.contains("wal: WalWriter")).to_equal(true)
```

</details>

#### has save_open_tab for tab persistence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session_db.spl")
expect(src.contains("me save_open_tab(doc_id: i64, path: text, cursor_row: i64, cursor_col: i64)")).to_equal(true)
expect(src.contains("me save_open_tab_with_folds(doc_id: i64, path: text, cursor_row: i64, cursor_col: i64, folds: text)")).to_equal(true)
expect(src.contains("folds=")).to_equal(true)
```

</details>

#### has save_editor_state for session state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session_db.spl")
expect(src.contains("me save_editor_state(active_doc_id: i64, mode: text, group_count: i64)")).to_equal(true)
```

</details>

#### has load_tabs and load_editor_state

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session_db.spl")
expect(src.contains("fn load_tabs() -> [SessionTabEntry]")).to_equal(true)
expect(src.contains("fn load_editor_state() -> SessionEditorState")).to_equal(true)
```

</details>

#### defines SessionTabEntry and SessionEditorState

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session_db.spl")
expect(src.contains("struct SessionTabEntry:")).to_equal(true)
expect(src.contains("folds: text")).to_equal(true)
expect(src.contains("struct SessionEditorState:")).to_equal(true)
```

</details>

#### wires session fold state to session DB restore

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me save_to_db(session_db: SessionDb)")).to_equal(true)
expect(src.contains("doc.buffer.fold_state()")).to_equal(true)
expect(src.contains("me restore_from_db(session_db: SessionDb)")).to_equal(true)
expect(src.contains("doc.buffer.restore_fold_state(session_tab_folds(tab))")).to_equal(true)
```

</details>

### editor recovery — crash safety

#### defines RecoveryManager class

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/recovery.spl")
expect(src.contains("class RecoveryManager:")).to_equal(true)
expect(src.contains("lock_path: text")).to_equal(true)
expect(src.contains("wal_path: text")).to_equal(true)
```

</details>

#### defines RecoveryState with needs_recovery flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/recovery.spl")
expect(src.contains("struct RecoveryState:")).to_equal(true)
expect(src.contains("needs_recovery: bool")).to_equal(true)
expect(src.contains("stale_lock: bool")).to_equal(true)
```

</details>

#### has check, acquire_lock, release_lock

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/recovery.spl")
expect(src.contains("fn check() -> RecoveryState")).to_equal(true)
expect(src.contains("me acquire_lock() -> bool")).to_equal(true)
expect(src.contains("me release_lock()")).to_equal(true)
```

</details>

#### has recover method that replays WAL

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/recovery.spl")
expect(src.contains("me recover(session_db: SessionDb) -> bool")).to_equal(true)
expect(src.contains("session_db.checkpoint()")).to_equal(true)
```

</details>

#### uses lock file with PID

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/recovery.spl")
expect(src.contains("editor.lock")).to_equal(true)
expect(src.contains("rt_process_id()")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_wal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor WAL — entry format
- editor WAL — checkpoint
- editor WAL — replay
- editor session DB — persistence
- editor recovery — crash safety

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
