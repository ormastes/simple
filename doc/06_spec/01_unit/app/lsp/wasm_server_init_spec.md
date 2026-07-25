# Wasm Server Init Specification

> <details>

<!-- sdn-diagram:id=wasm_server_init_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wasm_server_init_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wasm_server_init_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wasm_server_init_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wasm Server Init Specification

## Scenarios

### WASM LSP Server Initialization

#### ParserAdapter creation

#### creates core parser adapter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
expect(adapter.is_wasm_mode()).to_equal(true)
```

</details>

#### creates treesitter adapter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_treesitter()
expect(adapter.is_wasm_mode()).to_equal(false)
```

</details>

#### core adapter uses CoreParser backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
expect(adapter.backend).to_equal(ParserBackend.CoreParser)
```

</details>

#### treesitter adapter uses TreeSitter backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_treesitter()
expect(adapter.backend).to_equal(ParserBackend.TreeSitter)
```

</details>

#### ParserBackend enum

#### TreeSitter is distinct from CoreParser

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ts = ParserBackend.TreeSitter
val core = ParserBackend.CoreParser
expect(ts == core).to_equal(false)
```

</details>

#### ParseDiagnostic

#### creates diagnostic with line and column

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diag = ParseDiagnostic(
    line: 5, column: 10,
    end_line: 5, end_column: 15,
    message: "Unexpected token",
    severity: 1
)
expect(diag.line).to_equal(5)
expect(diag.column).to_equal(10)
expect(diag.message).to_equal("Unexpected token")
expect(diag.severity).to_equal(1)
```

</details>

#### creates warning diagnostic

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diag = ParseDiagnostic(
    line: 1, column: 0,
    end_line: 1, end_column: 5,
    message: "Unused variable",
    severity: 2
)
expect(diag.severity).to_equal(2)
```

</details>

#### ParseResult

#### creates successful result

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ParseResult(
    success: true,
    diagnostics: [],
    semantic_tokens: []
)
expect(result.success).to_equal(true)
expect(result.diagnostics.len()).to_equal(0)
```

</details>

#### creates result with diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val diag = ParseDiagnostic(
    line: 0, column: 0,
    end_line: 0, end_column: 1,
    message: "Error",
    severity: 1
)
val result = ParseResult(
    success: false,
    diagnostics: [diag],
    semantic_tokens: []
)
expect(result.success).to_equal(false)
expect(result.diagnostics.len()).to_equal(1)
```

</details>

#### Core parser parsing

#### parses valid Simple code

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val x = 42")
expect(result.success).to_equal(true)
expect(result.diagnostics.len()).to_equal(0)
```

</details>

#### parses multi-line code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("fn foo():\n    val x = 1\n    x")
expect(result.success).to_equal(true)
```

</details>

#### detects unmatched closing paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val x = )")
expect(result.success).to_equal(false)
expect(result.diagnostics.len()).to_be_greater_than(0)
expect(result.diagnostics[0].message).to_contain("parenthesis")
```

</details>

#### detects unmatched closing bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val x = ]")
expect(result.success).to_equal(false)
expect(result.diagnostics.len()).to_be_greater_than(0)
expect(result.diagnostics[0].message).to_contain("bracket")
```

</details>

#### parses empty source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("")
expect(result.success).to_equal(true)
```

</details>

#### parses comments only

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("# This is a comment")
expect(result.success).to_equal(true)
```

</details>

#### parses balanced parentheses

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val x = (1 + (2 * 3))")
expect(result.success).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp/wasm_server_init_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WASM LSP Server Initialization

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
