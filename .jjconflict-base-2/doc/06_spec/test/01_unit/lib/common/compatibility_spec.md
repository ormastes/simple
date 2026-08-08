# Compatibility Specification

> <details>

<!-- sdn-diagram:id=compatibility_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compatibility_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compatibility_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compatibility_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compatibility Specification

## Scenarios

### SDN Rust Compatibility

#### primitives

#### matches Rust for integers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("pos: 42\nneg: -17\nzero: 0\nlarge: 999999")
expect(result).to_equal(nil)
```

</details>

#### matches Rust for floats

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("pi: 3.14159\nneg: -2.718\nzero: 0.0")
expect(result).to_equal(nil)
```

</details>

#### matches Rust for strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("bare: hello")
expect(result).to_equal(nil)
```

</details>

#### matches Rust for booleans

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("yes: true\nno: false")
expect(result).to_equal(nil)
```

</details>

#### collections

#### matches Rust for inline arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("items = [1, 2, 3]")
expect(result).to_equal(nil)
```

</details>

#### matches Rust for block collections

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("config:\n    host: localhost\n    port: 8080")
expect(result).to_equal(nil)
```

</details>

#### serialization

#### produces compatible SDN output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("name: Alice\nage: 30\nactive: true")
expect(result).to_equal(nil)
```

</details>

#### produces compatible output for arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = parse("items = [1, 2, 3]")
expect(result).to_equal(nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compatibility_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SDN Rust Compatibility

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
