# Wasm Diagnostics Publish Specification

> <details>

<!-- sdn-diagram:id=wasm_diagnostics_publish_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wasm_diagnostics_publish_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wasm_diagnostics_publish_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wasm_diagnostics_publish_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wasm Diagnostics Publish Specification

## Scenarios

### WASM Diagnostics Publishing

#### Error diagnostics

#### produces no diagnostics for valid code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val x = 42")
expect(result.diagnostics.len()).to_equal(0)
```

</details>

#### produces diagnostic for unmatched close paren

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val x = (1 + 2))")
expect(result.diagnostics.len()).to_be_greater_than(0)
```

</details>

#### produces diagnostic for unmatched close bracket

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val arr = [1, 2]]")
expect(result.diagnostics.len()).to_be_greater_than(0)
```

</details>

#### Diagnostic accuracy

#### correct line number for first-line error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse(")")
expect(result.diagnostics[0].line).to_equal(0)
```

</details>

#### correct line number for second-line error

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val x = 1\n)")
val found_line1 = false
for diag in result.diagnostics:
    if diag.line == 1:
        var found_line1 = true
expect(result.diagnostics.len()).to_be_greater_than(0)
```

</details>

#### includes column span information

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse(")")
val diag = result.diagnostics[0]
expect(diag.column).to_equal(0)
```

</details>

#### Multiple errors

#### reports errors on multiple lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse(")\n]")
expect(result.diagnostics.len()).to_equal(2)
```

</details>

#### reports paren and bracket errors separately

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse(")\n]")
expect(result.diagnostics[0].message).to_contain("parenthesis")
expect(result.diagnostics[1].message).to_contain("bracket")
```

</details>

#### Valid patterns (no false positives)

#### balanced parens in function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("foo(bar(1, 2), baz(3))")
expect(result.diagnostics.len()).to_equal(0)
```

</details>

#### balanced brackets in array literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val a = [1, [2, 3], [4, [5]]]")
expect(result.diagnostics.len()).to_equal(0)
```

</details>

#### comments are ignored

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("# this has ) and ] but is a comment")
expect(result.diagnostics.len()).to_equal(0)
```

</details>

#### strings are part of valid code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val s = \"hello world\"")
expect(result.diagnostics.len()).to_equal(0)
```

</details>

#### Success flag

#### success is true when no diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse("val x = 1")
expect(result.success).to_equal(true)
```

</details>

#### success is false when diagnostics present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = ParserAdapter.create_core()
val result = adapter.parse(")")
expect(result.success).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/lsp/wasm_diagnostics_publish_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- WASM Diagnostics Publishing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
