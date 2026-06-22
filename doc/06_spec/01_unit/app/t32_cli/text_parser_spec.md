# Text Parser Specification

> <details>

<!-- sdn-diagram:id=text_parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=text_parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

text_parser_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=text_parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text Parser Specification

## Scenarios

### T32 Text Parser

#### splits whitespace-separated text

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = test_split_ws("hello   world   test")
expect(parts.len()).to_equal(3)
expect(parts[0]).to_equal("hello")
expect(parts[1]).to_equal("world")
```

</details>

#### handles tabs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = test_split_ws("a\tb\tc")
expect(parts.len()).to_equal(3)
```

</details>

#### handles leading whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = test_split_ws("   hello")
expect(parts.len()).to_equal(1)
expect(parts[0]).to_equal("hello")
```

</details>

#### parses register name=value pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val token = "R0=0x00000042"
val pair = token.split("=")
expect(pair.len()).to_equal(2)
expect(pair[0]).to_equal("R0")
expect(pair[1]).to_equal("0x00000042")
```

</details>

#### parses breakpoint line

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "E: 0x08001234 main Program Exec"
val parts = test_split_ws(line)
expect(parts[0]).to_equal("E:")
expect(parts[1]).to_equal("0x08001234")
expect(parts[2]).to_equal("main")
expect(parts[3]).to_equal("Program")
```

</details>

#### parses variable line

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "counter  int  42"
val parts = test_split_ws(line)
expect(parts[0]).to_equal("counter")
expect(parts[1]).to_equal("int")
expect(parts[2]).to_equal("42")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parts = test_split_ws("")
expect(parts.len()).to_equal(0)
```

</details>

#### formats table row

1. row push
   - Expected: row.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val row_data = ["count", "int", "42"]
var row: [text] = []
for item in row_data:
    row.push(item)
expect(row.len()).to_equal(3)
var joined = row[0]
joined = joined + "  " + row[1]
joined = joined + "  " + row[2]
expect(joined).to_contain("count")
expect(joined).to_contain("42")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/t32_cli/text_parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 Text Parser

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
