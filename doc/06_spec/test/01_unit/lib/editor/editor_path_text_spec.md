# Editor Path Text Specification

> <details>

<!-- sdn-diagram:id=editor_path_text_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_path_text_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_path_text_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_path_text_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Path Text Specification

## Scenarios

### editor shared path/text helpers

#### parses paths and filenames without app dependencies

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(editor_dirname("/vault/note.md")).to_equal("/vault")
expect(editor_path_basename("/vault/note.md")).to_equal("note.md")
expect(editor_join_path("/vault", "note.md")).to_equal("/vault/note.md")
expect(editor_join_path("/vault/", "note.md")).to_equal("/vault/note.md")
```

</details>

#### parses payload and numeric values

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(editor_payload_part("root|key|value", 1)).to_equal("key")
expect(editor_payload_csv("a, b,, c").len()).to_equal(3)
expect(editor_parse_i64("-42x", 7)).to_equal(-42)
expect(editor_parse_i64("x", 7)).to_equal(7)
```

</details>

#### normalizes relative dirs and markdown paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(editor_clean_relative_dir("./attachments/")).to_equal("attachments")
expect(editor_clean_relative_dir("/attachments/")).to_equal("attachments")
expect(editor_is_markdown_path("NOTE.MARKDOWN")).to_equal(true)
expect(editor_is_markdown_path("note.txt")).to_equal(false)
```

</details>

#### keeps GUI shell path and payload helpers in shared lib

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell = read_text("src/app/editor/gui_shell_render.spl")
val tui = read_text("src/app/editor/tui_shell.spl")
val tui_panels = read_text("src/app/editor/tui_shell_panels.spl")
expect(shell.contains("std.editor.core.path_text")).to_equal(true)
expect(shell.contains("fn _gui_shell_basename(")).to_equal(false)
expect(shell.contains("fn _gui_payload_part(")).to_equal(false)
expect(shell.contains("fn _gui_text_list_contains(")).to_equal(false)
expect(tui.contains("std.editor.core.path_text")).to_equal(true)
expect(tui.contains("fn _tui_is_markdown_path(")).to_equal(false)
expect(tui.contains("editor_is_markdown_path(path)")).to_equal(true)
expect(tui_panels.contains("std.editor.core.path_text")).to_equal(true)
expect(tui_panels.contains("fn _tui_basename(")).to_equal(false)
expect(tui_panels.contains("editor_path_basename(tab_path)")).to_equal(true)
```

</details>

#### keeps reusable editor modules on shared path helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val workspace = read_text("src/lib/editor/core/workspace.spl")
val ext_workspace = read_text("src/lib/editor/extensions/workspace.spl")
val ext_host = read_text("src/lib/editor/extensions/host.spl")
val debug_registry = read_text("src/lib/editor/services/debug_session_registry.spl")
val navigator = read_text("src/lib/editor/unified/project_navigator.spl")
val lsp_panel = read_text("src/lib/editor/view/lsp_result_panel.spl")
val diagnostics_panel = read_text("src/lib/editor/view/diagnostics_panel.spl")
val md_search = read_text("src/lib/editor/services/md_search.spl")
val file_watcher = read_text("src/lib/editor/services/file_watcher.spl")
val mcp_helpers = read_text("src/app/editor/mcp_tools_helpers.spl")
val attachment_template = read_text("src/app/editor/editor_attachment_template.spl")
val workspace_symbols = read_text("src/app/editor/editor_workspace_symbols.spl")
expect(workspace.contains("use std.editor.core.path_text")).to_equal(true)
expect(workspace.contains("fn _workspace_basename(")).to_equal(false)
expect(ext_workspace.contains("fn _workspace_basename(")).to_equal(false)
expect(ext_host.contains("fn _extension_host_dirname(")).to_equal(false)
expect(ext_host.contains("editor_dirname(file)")).to_equal(true)
expect(debug_registry.contains("fn _ed_dirname(")).to_equal(false)
expect(debug_registry.contains("fn _ed_basename(")).to_equal(false)
expect(navigator.contains("fn _basename(")).to_equal(false)
expect(lsp_panel.contains("fn _lsp_result_basename(")).to_equal(false)
expect(lsp_panel.contains("editor_path_basename(path) +")).to_equal(true)
expect(diagnostics_panel.contains("use std.editor.core.path_text")).to_equal(true)
expect(diagnostics_panel.contains("fn _diagnostics_panel_text_list_contains(")).to_equal(false)
expect(diagnostics_panel.contains("editor_text_list_contains(groups, group_key)")).to_equal(true)
expect(md_search.contains("use std.editor.core.path_text")).to_equal(true)
expect(md_search.contains("fn _md_vault_search_is_markdown_path(")).to_equal(false)
expect(md_search.contains("editor_is_markdown_path(path)")).to_equal(true)
expect(file_watcher.contains("use std.editor.core.path_text")).to_equal(true)
expect(file_watcher.contains("fn _fw_path_list_contains(")).to_equal(false)
expect(file_watcher.contains("editor_text_list_contains(dir.known_paths, path)")).to_equal(true)
expect(file_watcher.contains("editor_text_list_contains(current, path)")).to_equal(true)
expect(mcp_helpers.contains("fn editor_mcp_dirname(")).to_equal(false)
expect(mcp_helpers.contains("fn editor_mcp_path_basename(")).to_equal(false)
expect(mcp_helpers.contains("fn editor_mcp_last_dot(")).to_equal(false)
expect(mcp_helpers.contains("fn editor_mcp_clean_relative_dir(")).to_equal(false)
expect(mcp_helpers.contains("editor_dirname(target_path)")).to_equal(true)
expect(mcp_helpers.contains("editor_path_basename(attachment_path)")).to_equal(true)
expect(mcp_helpers.contains("editor_clean_relative_dir(storage_dir)")).to_equal(true)
expect(mcp_helpers.contains("editor_last_dot(name)")).to_equal(true)
expect(attachment_template.contains("app.editor.editor_path_text_helpers")).to_equal(false)
expect(attachment_template.contains("use std.editor.core.path_text")).to_equal(true)
expect(attachment_template.contains("editor_path_basename(file)")).to_equal(true)
expect(attachment_template.contains("editor_is_markdown_path(file)")).to_equal(true)
expect(workspace_symbols.contains("app.editor.editor_path_text_helpers")).to_equal(false)
expect(workspace_symbols.contains("use std.editor.core.path_text")).to_equal(true)
expect(workspace_symbols.contains("editor_find_text(trimmed, \")\")")).to_equal(true)
expect(workspace_symbols.contains("editor_find_text(line, name)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/editor/editor_path_text_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor shared path/text helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
