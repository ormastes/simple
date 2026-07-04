# Editor Workspace Specification

> <details>

<!-- sdn-diagram:id=editor_workspace_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_workspace_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_workspace_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_workspace_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Workspace Specification

## Scenarios

### editor workspace — config

#### defines WorkspaceFolder with path and name

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/workspace.spl")
expect(src.contains("struct WorkspaceFolder:")).to_equal(true)
expect(src.contains("path: text")).to_equal(true)
expect(src.contains("name: text")).to_equal(true)
```

</details>

#### defines WorkspaceConfig with folders and settings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/workspace.spl")
expect(src.contains("struct WorkspaceConfig:")).to_equal(true)
expect(src.contains("folders: [WorkspaceFolder]")).to_equal(true)
expect(src.contains("settings: [WorkspaceSetting]")).to_equal(true)
```

</details>

#### has workspace_new and workspace_load

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/workspace.spl")
expect(src.contains("fn workspace_new(root_path: text) -> WorkspaceConfig")).to_equal(true)
expect(src.contains("fn workspace_load(root_path: text) -> WorkspaceConfig")).to_equal(true)
```

</details>

#### has workspace_save for persistence

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/workspace.spl")
expect(src.contains("fn workspace_save(config: WorkspaceConfig) -> bool")).to_equal(true)
```

</details>

#### has setting get/set helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/workspace.spl")
expect(src.contains("fn workspace_get_setting(config: WorkspaceConfig, key: text, default_value: text) -> text")).to_equal(true)
expect(src.contains("fn workspace_set_setting(config: WorkspaceConfig, key: text, value: text) -> WorkspaceConfig")).to_equal(true)
```

</details>

#### uses .simple-editor/workspace.sdn as config path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/workspace.spl")
expect(src.contains(".simple-editor/workspace.sdn")).to_equal(true)
```

</details>

### editor file tree — navigation

#### defines FileTreeNode with path, name, kind, expanded

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/file_tree.spl")
expect(src.contains("struct FileTreeNode:")).to_equal(true)
expect(src.contains("path: text")).to_equal(true)
expect(src.contains("name: text")).to_equal(true)
expect(src.contains("kind: FileNodeKind")).to_equal(true)
expect(src.contains("expanded: bool")).to_equal(true)
```

</details>

#### defines FileTreeState struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/file_tree.spl")
expect(src.contains("struct FileTreeState:")).to_equal(true)
expect(src.contains("tree: FileTree")).to_equal(true)
expect(src.contains("selected_index: i64")).to_equal(true)
```

</details>

#### has select_next, select_prev, toggle_expand

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/file_tree.spl")
expect(src.contains("me select_next()")).to_equal(true)
expect(src.contains("me select_prev()")).to_equal(true)
expect(src.contains("me toggle_expand()")).to_equal(true)
```

</details>

#### has selected_path and selected_is_dir

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/file_tree.spl")
expect(src.contains("fn selected_path() -> text")).to_equal(true)
expect(src.contains("fn selected_is_dir() -> bool")).to_equal(true)
```

</details>

#### keeps directory state in reusable tree nodes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/file_tree.spl")
expect(src.contains("enum FileNodeKind:")).to_equal(true)
expect(src.contains("Directory")).to_equal(true)
expect(src.contains("children: [FileTreeNode]")).to_equal(true)
```

</details>

#### keeps file tree logic runtime neutral

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/view/file_tree.spl")
expect(src.contains("rt_dir_list")).to_equal(false)
```

</details>

### editor recent files — FIFO

#### defines RecentFiles struct with entries and max

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/recent.spl")
expect(src.contains("struct RecentFiles:")).to_equal(true)
expect(src.contains("entries: [text]")).to_equal(true)
expect(src.contains("max_entries: i64")).to_equal(true)
```

</details>

#### has recent_files_load and recent_files_save

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/recent.spl")
expect(src.contains("fn recent_files_load(storage_path: text) -> RecentFiles")).to_equal(true)
expect(src.contains("fn recent_files_save(recent: RecentFiles) -> bool")).to_equal(true)
```

</details>

#### has recent_files_add with deduplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/core/recent.spl")
expect(src.contains("fn recent_files_add(recent: RecentFiles, path: text) -> RecentFiles")).to_equal(true)
expect(src.contains("entry != path")).to_equal(true)
```

</details>

#### enforces max 50 entries with FIFO eviction

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
