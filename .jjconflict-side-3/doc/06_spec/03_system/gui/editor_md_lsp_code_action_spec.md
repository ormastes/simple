# Editor Md Lsp Code Action Specification

> <details>

<!-- sdn-diagram:id=editor_md_lsp_code_action_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_md_lsp_code_action_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_md_lsp_code_action_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_md_lsp_code_action_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Md Lsp Code Action Specification

## Scenarios

### Markdown LSP — code actions

#### advertises codeActionProvider

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/md_lsp/md_lsp_handler.spl")
expect(src.contains("codeActionProvider")).to_equal(true)
```

</details>

#### dispatches textDocument/codeAction

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/md_lsp/md_lsp_handler.spl")
expect(src.contains("fn md_lsp_code_action(params_json: text, req_id: i64, workspace: MdWorkspace) -> text")).to_equal(true)
expect(src.contains("if method == \"textDocument/codeAction\"")).to_equal(true)
```

</details>

#### builds quickfix actions for markdown warnings

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/app/md_lsp/md_lsp_handler.spl")
expect(src.contains("Apply Markdown quick fix")).to_equal(true)
expect(src.contains("\"quickfix\"")).to_equal(true)
expect(src.contains("_md_lsp_quickfix_line")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_md_lsp_code_action_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Markdown LSP — code actions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
