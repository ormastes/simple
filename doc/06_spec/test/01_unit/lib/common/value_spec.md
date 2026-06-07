# Value Specification

> <details>

<!-- sdn-diagram:id=value_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=value_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

value_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=value_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Value Specification

## Scenarios

### SDN Value

#### type checking

#### identifies null values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("v: null")
expect(result).to_equal(nil)
```

</details>

#### identifies boolean values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("v: true")
expect(result).to_equal(nil)
```

</details>

#### identifies integer values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("v: 42")
expect(result).to_equal(nil)
```

</details>

#### identifies float values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("v: 3.14")
expect(result).to_equal(nil)
```

</details>

#### identifies string values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("v: hello")
expect(result).to_equal(nil)
```

</details>

#### identifies dict values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("v:\n    a: 1")
expect(result).to_equal(nil)
```

</details>

#### identifies array values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("v = [1, 2, 3]")
expect(result).to_equal(nil)
```

</details>

#### type conversions

#### converts to bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("v: true")
expect(result).to_equal(nil)
```

</details>

#### converts to i64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("v: 42")
expect(result).to_equal(nil)
```

</details>

#### converts to f64

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("v: 3.14")
expect(result).to_equal(nil)
```

</details>

#### converts to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("v: hello")
expect(result).to_equal(nil)
```

</details>

#### returns None for invalid conversions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("v: null")
expect(result).to_equal(nil)
```

</details>

#### value methods

#### checks null value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("v: null")
expect(result).to_equal(nil)
```

</details>

#### gets bool value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("v: false")
expect(result).to_equal(nil)
```

</details>

#### gets int value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("v: 100")
expect(result).to_equal(nil)
```

</details>

#### gets string value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("v: test")
expect(result).to_equal(nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/value_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SDN Value

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
