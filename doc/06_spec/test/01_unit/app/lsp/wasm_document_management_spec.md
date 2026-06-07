# Wasm Document Management Specification

> <details>

<!-- sdn-diagram:id=wasm_document_management_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wasm_document_management_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wasm_document_management_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wasm_document_management_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wasm Document Management Specification

## Scenarios

### WASM Document Management

#### Parsing Simple documents

#### parses simple variable declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val name = \"Alice\"")
expect(result.success).to_equal(true)
```

</details>

#### parses mutable variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("var count = 0")
expect(result.success).to_equal(true)
```

</details>

#### parses function with body

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val code = "fn square(x: i64) -> i64:\n    x * x"
val result = adapter.parse(code)
expect(result.success).to_equal(true)
```

</details>

#### parses empty string

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

#### parses whitespace only

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("   \n   \n")
expect(result.success).to_equal(true)
```

</details>

#### Bracket error detection

#### reports error line for unmatched paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val x = )")
expect(result.diagnostics.len()).to_be_greater_than(0)
expect(result.diagnostics[0].line).to_equal(0)
expect(result.diagnostics[0].severity).to_equal(1)
```

</details>

#### reports error for unmatched bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val arr = ]")
expect(result.diagnostics.len()).to_be_greater_than(0)
expect(result.diagnostics[0].line).to_equal(0)
```

</details>

#### handles nested brackets correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val x = [[1, 2], [3, 4]]")
expect(result.success).to_equal(true)
```

</details>

#### handles mixed brackets and parens

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val x = foo([1, 2], (3 + 4))")
expect(result.success).to_equal(true)
```

</details>

#### Multi-line document parsing

#### parses describe/it test blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val code = "describe \"test\":\n    it \"works\":\n        expect(1).to_equal(1)"
val result = adapter.parse(code)
expect(result.success).to_equal(true)
```

</details>

#### parses class with methods

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val code = "class Counter:\n    count: i64\n    me increment():\n        self.count = self.count + 1"
val result = adapter.parse(code)
expect(result.success).to_equal(true)
```

</details>

#### parses enum definitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val code = "enum Color:\n    Red\n    Green\n    Blue"
val result = adapter.parse(code)
expect(result.success).to_equal(true)
```

</details>

#### Diagnostic properties

#### diagnostic has correct message for paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse(")")
expect(result.diagnostics[0].message).to_contain("parenthesis")
```

</details>

#### diagnostic has correct message for bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("]")
expect(result.diagnostics[0].message).to_contain("bracket")
```

</details>

#### diagnostic has error severity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse(")")
expect(result.diagnostics[0].severity).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp/wasm_document_management_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WASM Document Management

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
