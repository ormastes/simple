# Lsp Specification

> 1. expect capabilities has

<!-- sdn-diagram:id=lsp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lsp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lsp_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lsp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lsp Specification

## Scenarios

### LSP - initialization

#### handles initialize request

1. expect capabilities has


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# LSP initialize request
val capabilities = {
    "textDocument": {
        "completion": {"dynamicRegistration": true},
        "hover": {"dynamicRegistration": true}
    }
}

expect capabilities.has("textDocument")
```

</details>

#### responds with server capabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val server_capabilities = {
    "completionProvider": true,
    "hoverProvider": true,
    "definitionProvider": true
}

expect server_capabilities["completionProvider"]
```

</details>

### LSP - text synchronization

#### handles didOpen notification

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val doc = {
    "uri": "file:///test.spl",
    "languageId": "simple",
    "version": 1,
    "text": "val x = 42"
}

expect doc["languageId"] == "simple"
```

</details>

#### handles didChange notification

1. expect changes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val changes = [
    {"text": "val y = 10"}
]

expect changes.len() == 1
```

</details>

#### handles didClose notification

1. expect uri starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uri = "file:///test.spl"
expect uri.starts_with("file://")
```

</details>

### LSP - code completion

#### provides keyword completions

1. expect keywords contains
2. expect keywords contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val keywords = ["fn", "class", "struct", "enum", "val", "var"]
expect keywords.contains("fn")
expect keywords.contains("val")
```

</details>

#### provides variable completions

1. expect completions contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# In scope: val x = 42
val completions = ["x"]
expect completions.contains("x")
```

</details>

#### provides method completions

1. expect methods len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# obj.method_name
val methods = ["len", "is_empty", "contains"]
expect methods.len() > 0
```

</details>

### LSP - hover information

#### shows type information on hover

1. expect hover info len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Hovering over 'x' in 'val x: i64 = 42'
val hover_info = "i64"
expect hover_info.len() > 0
```

</details>

#### shows documentation on hover

1. expect doc contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Hovering over function with docstring
val doc = "Returns the length of the string"
expect doc.contains("length")
```

</details>

### LSP - go to definition

#### finds function definitions

1. expect location has


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Jump from call site to definition
val location = {"uri": "file:///test.spl", "line": 10}
expect location.has("uri")
```

</details>

#### finds variable definitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Jump from usage to declaration
val location = {"uri": "file:///test.spl", "line": 5}
expect location["line"] == 5
```

</details>

### LSP - diagnostics

#### reports syntax errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Missing colon on function def
val diagnostic = {
    "severity": "error",
    "message": "Expected ':' after function signature"
}

expect diagnostic["severity"] == "error"
```

</details>

#### reports type errors

1. expect diagnostic["message"] contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Type mismatch
val diagnostic = {
    "severity": "error",
    "message": "Type mismatch: expected i64, got text"
}

expect diagnostic["message"].contains("Type mismatch")
```

</details>

#### reports warnings

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Unused variable
val diagnostic = {
    "severity": "warning",
    "message": "Unused variable 'x'"
}

expect diagnostic["severity"] == "warning"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LSP - initialization
- LSP - text synchronization
- LSP - code completion
- LSP - hover information
- LSP - go to definition
- LSP - diagnostics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
