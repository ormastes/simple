# Lsp Handlers Specification

> <details>

<!-- sdn-diagram:id=lsp_handlers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lsp_handlers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lsp_handlers_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lsp_handlers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lsp Handlers Specification

## Scenarios

### LSP handler helpers

### lsp_handle_initialize

#### returns valid JSON-RPC response

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = lsp_handle_initialize("1")
expect(response).to_contain("jsonrpc")
expect(response).to_contain("2.0")
```

</details>

#### includes server info

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = lsp_handle_initialize("1")
expect(response).to_contain("simple-lsp")
expect(response).to_contain("0.1.0")
```

</details>

#### includes textDocumentSync capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = lsp_handle_initialize("1")
expect(response).to_contain("textDocumentSync")
```

</details>

#### includes hoverProvider

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = lsp_handle_initialize("1")
expect(response).to_contain("hoverProvider")
```

</details>

#### includes definitionProvider

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = lsp_handle_initialize("1")
expect(response).to_contain("definitionProvider")
```

</details>

#### includes documentSymbolProvider

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = lsp_handle_initialize("1")
expect(response).to_contain("documentSymbolProvider")
```

</details>

#### includes completionProvider with triggers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = lsp_handle_initialize("1")
expect(response).to_contain("completionProvider")
expect(response).to_contain("triggerCharacters")
```

</details>

#### includes save capability

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = lsp_handle_initialize("1")
expect(response).to_contain("save")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp_handlers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LSP handler helpers
- lsp_handle_initialize

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
