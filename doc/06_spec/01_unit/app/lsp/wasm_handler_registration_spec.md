# Wasm Handler Registration Specification

> <details>

<!-- sdn-diagram:id=wasm_handler_registration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wasm_handler_registration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wasm_handler_registration_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wasm_handler_registration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wasm Handler Registration Specification

## Scenarios

### WASM Handler Registration

#### Backend selection

#### core parser is WASM mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
expect(adapter.is_wasm_mode()).to_equal(true)
```

</details>

#### treesitter is not WASM mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_treesitter()
expect(adapter.is_wasm_mode()).to_equal(false)
```

</details>

#### core parser backend enum value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
expect(adapter.backend).to_equal(ParserBackend.CoreParser)
```

</details>

#### treesitter backend enum value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_treesitter()
expect(adapter.backend).to_equal(ParserBackend.TreeSitter)
```

</details>

#### Parser mode handling

#### core parser handles function definitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("fn hello():\n    print \"hi\"")
expect(result.success).to_equal(true)
```

</details>

#### core parser handles class definitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("class Foo:\n    x: i64")
expect(result.success).to_equal(true)
```

</details>

#### core parser handles struct definitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("struct Point:\n    x: i64\n    y: i64")
expect(result.success).to_equal(true)
```

</details>

#### core parser handles import statements

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("use std.text.\n")
expect(result.success).to_equal(true)
```

</details>

#### Error detection in WASM mode

#### detects extra closing paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("fn foo(x)): pass")
expect(result.success).to_equal(false)
```

</details>

#### detects extra closing bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val arr = [1, 2]]")
expect(result.success).to_equal(false)
```

</details>

#### does not report errors on valid code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val x = [1, 2, 3]")
expect(result.success).to_equal(true)
```

</details>

#### TreeSitter adapter fallback

#### treesitter parse returns success for any input

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_treesitter()
# TreeSitter path returns default success (actual parsing done elsewhere)
val result = adapter.parse("val x = 1")
expect(result.success).to_equal(true)
expect(result.diagnostics.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp/wasm_handler_registration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WASM Handler Registration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
