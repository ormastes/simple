# Parser Specification

> <details>

<!-- sdn-diagram:id=parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Parser Specification

## Scenarios

### SDN Parser

#### simple values

#### parses key-value pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("name: Alice")
expect(result).to_equal(nil)
```

</details>

#### parses multiple values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("name: Alice\nage: 30\ncity: NYC")
expect(result).to_equal(nil)
```

</details>

#### inline collections

#### parses inline dicts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "point = " + "{" + "xval: 10, yval: 20" + "}"
val result = parse(source)
expect(result).to_equal(nil)
```

</details>

#### parses inline arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("items = [1, 2, 3, 4, 5]")
expect(result).to_equal(nil)
```

</details>

#### parses nested inline collections

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = "{" + "xval: 10" + "}"
val source = "data = " + "{" + "items_list: [1, 2, 3], config: " + inner + "}"
val result = parse(source)
expect(result).to_equal(nil)
```

</details>

#### block collections

#### parses block dicts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("person:\n    name: Alice\n    age: 30")
expect(result).to_equal(nil)
```

</details>

#### parses block arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("numbers:\n    1\n    2\n    3")
expect(result).to_equal(nil)
```

</details>

#### disambiguates dict vs array blocks

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("config:\n    host: localhost\n    port: 8080")
expect(result).to_equal(nil)
```

</details>

#### error handling

#### reports syntax errors

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("key:")
expect(result).to_equal(nil)
```

</details>

#### reports unexpected tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("key. value")
expect(result).to_equal(nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/parser_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SDN Parser

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
