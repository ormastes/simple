# Editor Lsp Specification

> <details>

<!-- sdn-diagram:id=editor_lsp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_lsp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_lsp_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_lsp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Lsp Specification

## Scenarios

### editor LSP client — protocol

#### defines LspClient class

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("class LspClient:")).to_equal(true)
expect(src.contains("initialized: bool")).to_equal(true)
expect(src.contains("next_id: i64")).to_equal(true)
```

</details>

#### has initialize and shutdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("me initialize() -> LspResponse")).to_equal(true)
expect(src.contains("me shutdown()")).to_equal(true)
```

</details>

#### has did_open and did_change notifications

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("me did_open(path: text, content: text, language_id: text)")).to_equal(true)
expect(src.contains("me did_change(path: text, content: text, version: i64)")).to_equal(true)
```

</details>

#### has completion, definition, hover requests

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("me completion(path: text, line: i64, col: i64) -> LspResponse")).to_equal(true)
expect(src.contains("me definition(path: text, line: i64, col: i64) -> LspResponse")).to_equal(true)
expect(src.contains("me hover(path: text, line: i64, col: i64) -> LspResponse")).to_equal(true)
```

</details>

#### has code action requests for quick fixes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_client.spl")
val transport = read_text("src/lib/editor/services/lsp_transport.spl")
expect(src.contains("me code_action(path: text, line: i64, col: i64) -> LspResponse")).to_equal(true)
expect(src.contains("\"textDocument/codeAction\"")).to_equal(true)
expect(transport.contains("fn lsp_build_code_action_params(uri: text, line: i64, col: i64) -> text")).to_equal(true)
expect(transport.contains("quickfix")).to_equal(true)
```

</details>

#### uses textDocument URI format

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/lsp_client.spl")
expect(src.contains("textDocument")).to_equal(true)
expect(src.contains("lsp_path_to_uri")).to_equal(true)
```

</details>

### editor diagnostics — store

#### defines EditorDiagnostic struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/diagnostics.spl")
expect(src.contains("struct EditorDiagnostic:")).to_equal(true)
expect(src.contains("path: text")).to_equal(true)
expect(src.contains("severity: text")).to_equal(true)
expect(src.contains("message: text")).to_equal(true)
expect(src.contains("source: text")).to_equal(true)
```

</details>

#### defines DiagnosticStore class

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/diagnostics.spl")
expect(src.contains("class DiagnosticStore:")).to_equal(true)
```

</details>

#### has set_diagnostics and clear_diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/diagnostics.spl")
expect(src.contains("me set_diagnostics(path: text, diags: [EditorDiagnostic])")).to_equal(true)
expect(src.contains("me clear_diagnostics(path: text)")).to_equal(true)
```

</details>

#### provides error_count and warning_count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/diagnostics.spl")
expect(src.contains("fn error_count() -> i64")).to_equal(true)
expect(src.contains("fn warning_count() -> i64")).to_equal(true)
```

</details>

#### tracks LSP code actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/diagnostics.spl")
expect(src.contains("struct EditorCodeAction:")).to_equal(true)
expect(src.contains("fn diagnostics_handle_code_actions(store: DiagnosticStore, path: text, result_json: text) -> [EditorCodeAction]")).to_equal(true)
expect(src.contains("fn code_actions_handle_response(result_json: text) -> [EditorCodeAction]")).to_equal(true)
```

</details>

#### replaces diagnostics for one publishDiagnostics URI and clears empty publishes

1. EditorDiagnostic
2. EditorDiagnostic
   - Expected: diagnostics_publish_path(publish_one) equals `first_path`
   - Expected: diagnostics_publish_version(publish_one) equals `2`
3. store = diagnostics store with publish
   - Expected: store.total_count() equals `2`
   - Expected: first_diags.len() equals `1`
   - Expected: first_diags[0].line equals `1`
   - Expected: first_diags[0].col equals `4`
   - Expected: first_diags[0].severity equals `error`
   - Expected: first_diags[0].message equals `fresh`
   - Expected: store.diagnostics_for(other_path).len() equals `1`
4. store = diagnostics store with publish
   - Expected: store.diagnostics_for(first_path).len() equals `1`
   - Expected: store.diagnostics_for(first_path)[0].message equals `fresh`
5. store = diagnostics store with publish
   - Expected: store.diagnostics_for(first_path).len() equals `0`
   - Expected: store.diagnostics_for(other_path).len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first_path = "/tmp/simple_editor_lsp_publish_first.spl"
val other_path = "/tmp/simple_editor_lsp_publish_other.spl"
var store = DiagnosticStore(diagnostics: [
    EditorDiagnostic(path: first_path, line: 9, col: 1, end_line: 9, end_col: 2, severity: "warning", message: "stale", source: "test"),
    EditorDiagnostic(path: other_path, line: 3, col: 1, end_line: 3, end_col: 2, severity: "error", message: "keep", source: "test")
], publish_versions: [])
val publish_one = "{\"uri\":\"file://" + first_path + "\",\"version\":2,\"diagnostics\":[{\"range\":{\"start\":{\"line\":1,\"character\":4},\"end\":{\"line\":1,\"character\":8}},\"severity\":1,\"source\":\"simple\",\"message\":\"fresh\"}]}"

expect(diagnostics_publish_path(publish_one)).to_equal(first_path)
expect(diagnostics_publish_version(publish_one)).to_equal(2)
store = diagnostics_store_with_publish(store, publish_one)

expect(store.total_count()).to_equal(2)
val first_diags = store.diagnostics_for(first_path)
expect(first_diags.len()).to_equal(1)
if first_diags.len() > 0:
    expect(first_diags[0].line).to_equal(1)
    expect(first_diags[0].col).to_equal(4)
    expect(first_diags[0].severity).to_equal("error")
    expect(first_diags[0].message).to_equal("fresh")
expect(store.diagnostics_for(other_path).len()).to_equal(1)

val stale_publish = "{\"uri\":\"file://" + first_path + "\",\"version\":1,\"diagnostics\":[{\"range\":{\"start\":{\"line\":5,\"character\":1},\"end\":{\"line\":5,\"character\":2}},\"severity\":2,\"source\":\"simple\",\"message\":\"old\"}]}"
store = diagnostics_store_with_publish(store, stale_publish)

expect(store.diagnostics_for(first_path).len()).to_equal(1)
expect(store.diagnostics_for(first_path)[0].message).to_equal("fresh")

val clear_first = "{\"uri\":\"file://" + first_path + "\",\"version\":3,\"diagnostics\":[]}"
store = diagnostics_store_with_publish(store, clear_first)

expect(store.diagnostics_for(first_path).len()).to_equal(0)
expect(store.diagnostics_for(other_path).len()).to_equal(1)
```

</details>

### editor LSP configs — language servers

#### has Markdown and Simple LSP code action wrappers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val md = read_text("src/lib/editor/services/md_lsp_config.spl")
val simple = read_text("src/lib/editor/services/simple_lsp_config.spl")
expect(md.contains("fn md_lsp_code_action(state: MdLspState, path: text, line: i64, col: i64) -> LspResponse")).to_equal(true)
expect(simple.contains("fn simple_lsp_code_action(state: SimpleLspState, path: text, line: i64, col: i64) -> LspResponse")).to_equal(true)
expect(simple.contains("server_command: \"bin/simple lsp\"")).to_equal(true)
```

</details>

### editor completion — popup

#### defines CompletionItem and CompletionState

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/completion.spl")
expect(src.contains("struct CompletionItem:")).to_equal(true)
expect(src.contains("class CompletionState:")).to_equal(true)
expect(src.contains("visible: bool")).to_equal(true)
```

</details>

#### has show, hide, select_next, select_prev

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/completion.spl")
expect(src.contains("me show(items: [CompletionItem], prefix: text)")).to_equal(true)
expect(src.contains("me hide()")).to_equal(true)
expect(src.contains("me select_next()")).to_equal(true)
expect(src.contains("me select_prev()")).to_equal(true)
```

</details>

### editor file watcher — polling

#### defines FileWatcher class

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/file_watcher.spl")
expect(src.contains("class FileWatcher:")).to_equal(true)
expect(src.contains("poll_interval_ms: i64")).to_equal(true)
expect(src.contains("ignore_globs: [text]")).to_equal(true)
```

</details>

#### has watch, unwatch, check_changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/file_watcher.spl")
expect(src.contains("me watch(path: text)")).to_equal(true)
expect(src.contains("me unwatch(path: text)")).to_equal(true)
expect(src.contains("me check_changes() -> [text]")).to_equal(true)
expect(src.contains("me check_events_debounced(elapsed_ms: i64)")).to_equal(true)
expect(src.contains("me configure_policy(poll_interval_ms: i64, ignore_globs: [text])")).to_equal(true)
```

</details>

#### uses content hash for change detection

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/file_watcher.spl")
expect(src.contains("last_hash: i64")).to_equal(true)
expect(src.contains("fn _fw_hash(content: text) -> i64")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_lsp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor LSP client — protocol
- editor diagnostics — store
- editor LSP configs — language servers
- editor completion — popup
- editor file watcher — polling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
