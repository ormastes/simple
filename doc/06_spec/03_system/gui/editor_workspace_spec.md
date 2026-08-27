# Editor Workspace Specification

> Tests covering editor workspace — config, editor file tree — navigation, editor recent files — FIFO.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Workspace Specification

## Scenarios

### editor workspace — config

#### defines WorkspaceFolder with path and name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines WorkspaceFolder with path and name
   - Expected: src contains `struct WorkspaceFolder:`
   - Expected: src contains `path: text`
   - Expected: src contains `name: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines WorkspaceFolder with path and name")
val src = read_text("src/lib/editor/core/workspace.spl")
expect(src.contains("struct WorkspaceFolder:")).to_equal(true)
expect(src.contains("path: text")).to_equal(true)
expect(src.contains("name: text")).to_equal(true)
```

</details>

#### defines WorkspaceConfig with folders and settings

- defines WorkspaceConfig with folders and settings
   - Expected: src contains `struct WorkspaceConfig:`
   - Expected: src contains `folders: [WorkspaceFolder]`
   - Expected: src contains `settings: [WorkspaceSetting]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines WorkspaceConfig with folders and settings")
val src = read_text("src/lib/editor/core/workspace.spl")
expect(src.contains("struct WorkspaceConfig:")).to_equal(true)
expect(src.contains("folders: [WorkspaceFolder]")).to_equal(true)
expect(src.contains("settings: [WorkspaceSetting]")).to_equal(true)
```

</details>

#### has workspace_new and workspace_load

- has workspace_new and workspace_load
   - Expected: src contains `fn workspace_new(root_path: text) -> WorkspaceConfig`
   - Expected: src contains `fn workspace_load(root_path: text) -> WorkspaceConfig`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has workspace_new and workspace_load")
val src = read_text("src/lib/editor/core/workspace.spl")
expect(src.contains("fn workspace_new(root_path: text) -> WorkspaceConfig")).to_equal(true)
expect(src.contains("fn workspace_load(root_path: text) -> WorkspaceConfig")).to_equal(true)
```

</details>

#### has workspace_save for persistence

- has workspace_save for persistence
   - Expected: src contains `fn workspace_save(config: WorkspaceConfig) -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has workspace_save for persistence")
val src = read_text("src/lib/editor/core/workspace.spl")
expect(src.contains("fn workspace_save(config: WorkspaceConfig) -> bool")).to_equal(true)
```

</details>

#### has setting get/set helpers

- has setting get/set helpers
   - Expected: src contains `fn workspace_get_setting(config: WorkspaceConfig, key: text, default_value: t... (full value in folded executable source)`
   - Expected: src contains `fn workspace_set_setting(config: WorkspaceConfig, key: text, value: text) -> ... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has setting get/set helpers")
val src = read_text("src/lib/editor/core/workspace.spl")
expect(src.contains("fn workspace_get_setting(config: WorkspaceConfig, key: text, default_value: text) -> text")).to_equal(true)
expect(src.contains("fn workspace_set_setting(config: WorkspaceConfig, key: text, value: text) -> WorkspaceConfig")).to_equal(true)
```

</details>

#### uses .simple-editor/workspace.sdn as config path

- uses .simple-editor/workspace.sdn as config path
   - Expected: src contains `.simple-editor/workspace.sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses .simple-editor/workspace.sdn as config path")
val src = read_text("src/lib/editor/core/workspace.spl")
expect(src.contains(".simple-editor/workspace.sdn")).to_equal(true)
```

</details>

### editor file tree — navigation

#### defines FileTreeNode with path, name, kind, expanded

- defines FileTreeNode with path, name, kind, expanded
   - Expected: src contains `struct FileTreeNode:`
   - Expected: src contains `path: text`
   - Expected: src contains `name: text`
   - Expected: src contains `kind: FileNodeKind`
   - Expected: src contains `expanded: bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines FileTreeNode with path, name, kind, expanded")
val src = read_text("src/lib/editor/view/file_tree.spl")
expect(src.contains("struct FileTreeNode:")).to_equal(true)
expect(src.contains("path: text")).to_equal(true)
expect(src.contains("name: text")).to_equal(true)
expect(src.contains("kind: FileNodeKind")).to_equal(true)
expect(src.contains("expanded: bool")).to_equal(true)
```

</details>

#### defines FileTreeState struct

- defines FileTreeState struct
   - Expected: src contains `struct FileTreeState:`
   - Expected: src contains `tree: FileTree`
   - Expected: src contains `selected_index: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines FileTreeState struct")
val src = read_text("src/lib/editor/view/file_tree.spl")
expect(src.contains("struct FileTreeState:")).to_equal(true)
expect(src.contains("tree: FileTree")).to_equal(true)
expect(src.contains("selected_index: i64")).to_equal(true)
```

</details>

#### has select_next, select_prev, toggle_expand

- has select_next, select_prev, toggle_expand
   - Expected: src contains `me select_next()`
   - Expected: src contains `me select_prev()`
   - Expected: src contains `me toggle_expand()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has select_next, select_prev, toggle_expand")
val src = read_text("src/lib/editor/view/file_tree.spl")
expect(src.contains("me select_next()")).to_equal(true)
expect(src.contains("me select_prev()")).to_equal(true)
expect(src.contains("me toggle_expand()")).to_equal(true)
```

</details>

#### has selected_path and selected_is_dir

- has selected_path and selected_is_dir
   - Expected: src contains `fn selected_path() -> text`
   - Expected: src contains `fn selected_is_dir() -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has selected_path and selected_is_dir")
val src = read_text("src/lib/editor/view/file_tree.spl")
expect(src.contains("fn selected_path() -> text")).to_equal(true)
expect(src.contains("fn selected_is_dir() -> bool")).to_equal(true)
```

</details>

#### keeps directory state in reusable tree nodes

- keeps directory state in reusable tree nodes
   - Expected: src contains `enum FileNodeKind:`
   - Expected: src contains `Directory`
   - Expected: src contains `children: [FileTreeNode]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps directory state in reusable tree nodes")
val src = read_text("src/lib/editor/view/file_tree.spl")
expect(src.contains("enum FileNodeKind:")).to_equal(true)
expect(src.contains("Directory")).to_equal(true)
expect(src.contains("children: [FileTreeNode]")).to_equal(true)
```

</details>

#### keeps file tree logic runtime neutral

- keeps file tree logic runtime neutral
   - Expected: src does not contain `rt_dir_list`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps file tree logic runtime neutral")
val src = read_text("src/lib/editor/view/file_tree.spl")
expect(src.contains("rt_dir_list")).to_equal(false)
```

</details>

### editor recent files — FIFO

#### defines RecentFiles struct with entries and max

- defines RecentFiles struct with entries and max
   - Expected: src contains `struct RecentFiles:`
   - Expected: src contains `entries: [text]`
   - Expected: src contains `max_entries: i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines RecentFiles struct with entries and max")
val src = read_text("src/lib/editor/core/recent.spl")
expect(src.contains("struct RecentFiles:")).to_equal(true)
expect(src.contains("entries: [text]")).to_equal(true)
expect(src.contains("max_entries: i64")).to_equal(true)
```

</details>

#### has recent_files_load and recent_files_save

- has recent_files_load and recent_files_save
   - Expected: src contains `fn recent_files_load(storage_path: text) -> RecentFiles`
   - Expected: src contains `fn recent_files_save(recent: RecentFiles) -> bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has recent_files_load and recent_files_save")
val src = read_text("src/lib/editor/core/recent.spl")
expect(src.contains("fn recent_files_load(storage_path: text) -> RecentFiles")).to_equal(true)
expect(src.contains("fn recent_files_save(recent: RecentFiles) -> bool")).to_equal(true)
```

</details>

#### has recent_files_add with deduplication

- has recent_files_add with deduplication
   - Expected: src contains `fn recent_files_add(recent: RecentFiles, path: text) -> RecentFiles`
   - Expected: src contains `entry != path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has recent_files_add with deduplication")
val src = read_text("src/lib/editor/core/recent.spl")
expect(src.contains("fn recent_files_add(recent: RecentFiles, path: text) -> RecentFiles")).to_equal(true)
expect(src.contains("entry != path")).to_equal(true)
```

</details>

#### enforces max 50 entries with FIFO eviction

- enforces max 50 entries with FIFO eviction
   - Expected: src contains `new_entries.len() > recent.max_entries`
   - Expected: src contains `max_entries: 50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enforces max 50 entries with FIFO eviction")
val src = read_text("src/lib/editor/core/recent.spl")
expect(src.contains("new_entries.len() > recent.max_entries")).to_equal(true)
expect(src.contains("max_entries: 50")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_workspace_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering editor workspace — config, editor file tree — navigation, editor recent files — FIFO.
- editor workspace — config
- editor file tree — navigation
- editor recent files — FIFO

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `3fc159345d734f5fd072753b74516e261b778380637ef76a4e6bd048c50107b0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3fc159345d734f5fd072753b74516e261b778380637ef76a4e6bd048c50107b0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3fc159345d734f5fd072753b74516e261b778380637ef76a4e6bd048c50107b0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/editor_workspace_spec.spl
mirror: doc/06_spec/03_system/gui/editor_workspace_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_workspace_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_workspace_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_workspace_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines WorkspaceFolder with path and name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_workspace_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines WorkspaceConfig with folders and settings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_workspace_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has workspace_new and workspace_load' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
