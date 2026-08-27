# Editor Wal Specification

> Tests covering editor WAL — entry format, editor WAL — checkpoint, editor WAL — replay, editor session DB — persistence, editor recovery — crash safety.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Wal Specification

## Scenarios

### editor WAL — entry format

#### defines WalEntry with sequence, table, operation, key, data_sdn

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines WalEntry with sequence, table, operation, key, data_sdn
   - Expected: src contains `struct WalEntry:`
   - Expected: src contains `sequence: i64`
   - Expected: src contains `table: text`
   - Expected: src contains `operation: text`
   - Expected: src contains `key: text`
   - Expected: src contains `data_sdn: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines WalEntry with sequence, table, operation, key, data_sdn")
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

- defines WalWriter with wal_path and checkpoint_threshold
   - Expected: src contains `class WalWriter:`
   - Expected: src contains `wal_path: text`
   - Expected: src contains `checkpoint_threshold: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines WalWriter with wal_path and checkpoint_threshold")
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("class WalWriter:")).to_equal(true)
expect(src.contains("wal_path: text")).to_equal(true)
expect(src.contains("checkpoint_threshold: i64")).to_equal(true)
```

</details>

#### has append, append_set, append_delete methods

- has append, append_set, append_delete methods
   - Expected: src contains `me append(table: text, operation: text, key: text, data_sdn: text) -> bool`
   - Expected: src contains `me append_set(table: text, key: text, data_sdn: text) -> bool`
   - Expected: src contains `me append_delete(table: text, key: text) -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has append, append_set, append_delete methods")
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("me append(table: text, operation: text, key: text, data_sdn: text) -> bool")).to_equal(true)
expect(src.contains("me append_set(table: text, key: text, data_sdn: text) -> bool")).to_equal(true)
expect(src.contains("me append_delete(table: text, key: text) -> bool")).to_equal(true)
```

</details>

#### uses WAL| prefix format for entries

- uses WAL| prefix format for entries
   - Expected: src contains `WAL|`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses WAL| prefix format for entries")
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("WAL|")).to_equal(true)
```

</details>

### editor WAL — checkpoint

#### has checkpoint method

- has checkpoint method
   - Expected: src contains `me checkpoint() -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has checkpoint method")
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("me checkpoint() -> bool")).to_equal(true)
```

</details>

#### writes to temp file then renames for atomicity

- writes to temp file then renames for atomicity
   - Expected: src contains `me.db_path + ".tmp"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes to temp file then renames for atomicity")
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("me.db_path + \".tmp\"")).to_equal(true)
```

</details>

#### clears WAL after successful checkpoint

- clears WAL after successful checkpoint
   - Expected: src contains `me.entry_count = 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clears WAL after successful checkpoint")
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("me.entry_count = 0")).to_equal(true)
```

</details>

#### auto-checkpoints at threshold

- auto-checkpoints at threshold
   - Expected: src contains `me.entry_count >= me.checkpoint_threshold`
   - Expected: src contains `me.checkpoint()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("auto-checkpoints at threshold")
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("me.entry_count >= me.checkpoint_threshold")).to_equal(true)
expect(src.contains("me.checkpoint()")).to_equal(true)
```

</details>

### editor WAL — replay

#### defines WalReader class

- defines WalReader class
   - Expected: src contains `class WalReader:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines WalReader class")
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("class WalReader:")).to_equal(true)
```

</details>

#### has read_entries and has_entries

- has read_entries and has_entries
   - Expected: src contains `fn read_entries() -> [WalEntry]`
   - Expected: src contains `fn has_entries() -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has read_entries and has_entries")
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("fn read_entries() -> [WalEntry]")).to_equal(true)
expect(src.contains("fn has_entries() -> bool")).to_equal(true)
```

</details>

#### parses WAL entries from content

- parses WAL entries from content
   - Expected: src contains `fn wal_parse_entries(content: text) -> [WalEntry]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses WAL entries from content")
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("fn wal_parse_entries(content: text) -> [WalEntry]")).to_equal(true)
```

</details>

#### applies entries to merge with existing DB

- applies entries to merge with existing DB
   - Expected: src contains `fn _wal_apply_entries(db_content: text, entries: [WalEntry]) -> text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies entries to merge with existing DB")
val src = read_text("src/lib/editor/core/wal.spl")
expect(src.contains("fn _wal_apply_entries(db_content: text, entries: [WalEntry]) -> text")).to_equal(true)
```

</details>

### editor session DB — persistence

#### defines SessionDb class

- defines SessionDb class
   - Expected: src contains `class SessionDb:`
   - Expected: src contains `wal: WalWriter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines SessionDb class")
val src = read_text("src/lib/editor/core/session_db.spl")
expect(src.contains("class SessionDb:")).to_equal(true)
expect(src.contains("wal: WalWriter")).to_equal(true)
```

</details>

#### has save_open_tab for tab persistence

- has save_open_tab for tab persistence
   - Expected: src contains `me save_open_tab(doc_id: i64, path: text, cursor_row: i64, cursor_col: i64)`
   - Expected: src contains `me save_open_tab_with_folds(doc_id: i64, path: text, cursor_row: i64, cursor_... (full value in folded executable source)`
   - Expected: src contains `folds=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has save_open_tab for tab persistence")
val src = read_text("src/lib/editor/core/session_db.spl")
expect(src.contains("me save_open_tab(doc_id: i64, path: text, cursor_row: i64, cursor_col: i64)")).to_equal(true)
expect(src.contains("me save_open_tab_with_folds(doc_id: i64, path: text, cursor_row: i64, cursor_col: i64, folds: text)")).to_equal(true)
expect(src.contains("folds=")).to_equal(true)
```

</details>

#### has save_editor_state for session state

- has save_editor_state for session state
   - Expected: src contains `me save_editor_state(active_doc_id: i64, mode: text, group_count: i64)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has save_editor_state for session state")
val src = read_text("src/lib/editor/core/session_db.spl")
expect(src.contains("me save_editor_state(active_doc_id: i64, mode: text, group_count: i64)")).to_equal(true)
```

</details>

#### has load_tabs and load_editor_state

- has load_tabs and load_editor_state
   - Expected: src contains `fn load_tabs() -> [SessionTabEntry]`
   - Expected: src contains `fn load_editor_state() -> SessionEditorState`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has load_tabs and load_editor_state")
val src = read_text("src/lib/editor/core/session_db.spl")
expect(src.contains("fn load_tabs() -> [SessionTabEntry]")).to_equal(true)
expect(src.contains("fn load_editor_state() -> SessionEditorState")).to_equal(true)
```

</details>

#### defines SessionTabEntry and SessionEditorState

- defines SessionTabEntry and SessionEditorState
   - Expected: src contains `struct SessionTabEntry:`
   - Expected: src contains `folds: text`
   - Expected: src contains `struct SessionEditorState:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines SessionTabEntry and SessionEditorState")
val src = read_text("src/lib/editor/core/session_db.spl")
expect(src.contains("struct SessionTabEntry:")).to_equal(true)
expect(src.contains("folds: text")).to_equal(true)
expect(src.contains("struct SessionEditorState:")).to_equal(true)
```

</details>

#### wires session fold state to session DB restore

- wires session fold state to session DB restore
   - Expected: src contains `me save_to_db(session_db: SessionDb)`
   - Expected: src contains `doc.buffer.fold_state()`
   - Expected: src contains `me restore_from_db(session_db: SessionDb)`
   - Expected: src contains `doc.buffer.restore_fold_state(session_tab_folds(tab))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wires session fold state to session DB restore")
val src = read_text("src/lib/editor/core/session.spl")
expect(src.contains("me save_to_db(session_db: SessionDb)")).to_equal(true)
expect(src.contains("doc.buffer.fold_state()")).to_equal(true)
expect(src.contains("me restore_from_db(session_db: SessionDb)")).to_equal(true)
expect(src.contains("doc.buffer.restore_fold_state(session_tab_folds(tab))")).to_equal(true)
```

</details>

### editor recovery — crash safety

#### defines RecoveryManager class

- defines RecoveryManager class
   - Expected: src contains `class RecoveryManager:`
   - Expected: src contains `lock_path: text`
   - Expected: src contains `wal_path: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines RecoveryManager class")
val src = read_text("src/lib/editor/core/recovery.spl")
expect(src.contains("class RecoveryManager:")).to_equal(true)
expect(src.contains("lock_path: text")).to_equal(true)
expect(src.contains("wal_path: text")).to_equal(true)
```

</details>

#### defines RecoveryState with needs_recovery flag

- defines RecoveryState with needs_recovery flag
   - Expected: src contains `struct RecoveryState:`
   - Expected: src contains `needs_recovery: bool`
   - Expected: src contains `stale_lock: bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines RecoveryState with needs_recovery flag")
val src = read_text("src/lib/editor/core/recovery.spl")
expect(src.contains("struct RecoveryState:")).to_equal(true)
expect(src.contains("needs_recovery: bool")).to_equal(true)
expect(src.contains("stale_lock: bool")).to_equal(true)
```

</details>

#### has check, acquire_lock, release_lock

- has check, acquire_lock, release_lock
   - Expected: src contains `fn check() -> RecoveryState`
   - Expected: src contains `me acquire_lock() -> bool`
   - Expected: src contains `me release_lock()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has check, acquire_lock, release_lock")
val src = read_text("src/lib/editor/core/recovery.spl")
expect(src.contains("fn check() -> RecoveryState")).to_equal(true)
expect(src.contains("me acquire_lock() -> bool")).to_equal(true)
expect(src.contains("me release_lock()")).to_equal(true)
```

</details>

#### has recover method that replays WAL

- has recover method that replays WAL
   - Expected: src contains `me recover(session_db: SessionDb) -> bool`
   - Expected: src contains `session_db.checkpoint()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has recover method that replays WAL")
val src = read_text("src/lib/editor/core/recovery.spl")
expect(src.contains("me recover(session_db: SessionDb) -> bool")).to_equal(true)
expect(src.contains("session_db.checkpoint()")).to_equal(true)
```

</details>

#### uses lock file with PID

- uses lock file with PID
   - Expected: src contains `editor.lock`
   - Expected: src contains `rt_process_id()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses lock file with PID")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering editor WAL — entry format, editor WAL — checkpoint, editor WAL — replay, editor session DB — persistence, editor recovery — crash safety.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7872b224c8a374bf494c02d4031d1e3fce98bef840143af8cd1cc44fbf2f8b28`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7872b224c8a374bf494c02d4031d1e3fce98bef840143af8cd1cc44fbf2f8b28`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7872b224c8a374bf494c02d4031d1e3fce98bef840143af8cd1cc44fbf2f8b28`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/editor_wal_spec.spl
mirror: doc/06_spec/03_system/gui/editor_wal_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_wal_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_wal_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_wal_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines WalEntry with sequence, table, operation, key, data_sdn' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_wal_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines WalWriter with wal_path and checkpoint_threshold' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_wal_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has append, append_set, append_delete methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
