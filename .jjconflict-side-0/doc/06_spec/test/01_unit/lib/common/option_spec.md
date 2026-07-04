# Option Specification

> <details>

<!-- sdn-diagram:id=option_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=option_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

option_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=option_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Option Specification

## Scenarios

### Option stdlib

### option_is_some and option_is_none

#### is_some returns true for non-nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(option_is_some(42)).to_equal(true)
```

</details>

#### is_some returns false for nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(option_is_some(nil)).to_equal(false)
```

</details>

#### is_none returns true for nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(option_is_none(nil)).to_equal(true)
```

</details>

#### is_none returns false for non-nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(option_is_none("hello")).to_equal(false)
```

</details>

### option_unwrap_or

#### returns value when some

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(option_unwrap_or(10, 99)).to_equal(10)
```

</details>

#### returns default when nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(option_unwrap_or(nil, 99)).to_equal(99)
```

</details>

### option_map

#### maps some value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_map(5, fn(x): x * 2)
expect(result).to_equal(10)
```

</details>

#### returns nil for nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_map(nil, fn(x): x * 2)
expect(result).to_be_nil()
```

</details>

### option_filter

#### returns value when predicate true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_filter(10, fn(x): x > 5)
expect(result).to_equal(10)
```

</details>

#### returns nil when predicate false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_filter(3, fn(x): x > 5)
expect(result).to_be_nil()
```

</details>

#### returns nil for nil input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_filter(nil, fn(x): x > 5)
expect(result).to_be_nil()
```

</details>

### option_flat_map

#### chains some to some

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_flat_map(5, fn(x): x * 3)
expect(result).to_equal(15)
```

</details>

#### returns nil for nil input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_flat_map(nil, fn(x): x * 3)
expect(result).to_be_nil()
```

</details>

### option_or_else

#### returns original when some

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_or_else(42, fn(): 99)
expect(result).to_equal(42)
```

</details>

#### calls alternative when nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_or_else(nil, fn(): 99)
expect(result).to_equal(99)
```

</details>

### option_zip

#### zips two some values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_zip(1, 2)
expect(result).to_equal([1, 2])
```

</details>

#### returns nil when first is nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_zip(nil, 2)
expect(result).to_be_nil()
```

</details>

#### returns nil when second is nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_zip(1, nil)
expect(result).to_be_nil()
```

</details>

### option_inspect

#### does not error on some

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# option_inspect applies side effect; we verify it returns the value
val result = option_inspect(42, fn(x): x + 0)
expect(result).to_equal(42)
```

</details>

#### does not error on nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = option_inspect(nil, fn(x): x + 0)
expect(result).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/option_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Option stdlib
- option_is_some and option_is_none
- option_unwrap_or
- option_map
- option_filter
- option_flat_map
- option_or_else
- option_zip
- option_inspect

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
