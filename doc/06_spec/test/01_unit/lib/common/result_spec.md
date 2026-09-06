# Result Specification

> <details>

<!-- sdn-diagram:id=result_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=result_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

result_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=result_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Result Specification

## Scenarios

### Result stdlib

### result_is_ok and result_is_err

#### is_ok returns true for non-nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(result_is_ok(42)).to_equal(true)
```

</details>

#### is_ok returns false for nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(result_is_ok(nil)).to_equal(false)
```

</details>

#### is_err returns true for nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(result_is_err(nil)).to_equal(true)
```

</details>

#### is_err returns false for non-nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(result_is_err("ok")).to_equal(false)
```

</details>

### result_unwrap_or

#### returns value when ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(result_unwrap_or(10, 99)).to_equal(10)
```

</details>

#### returns default when nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(result_unwrap_or(nil, 99)).to_equal(99)
```

</details>

### result_map

#### maps ok value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_map(5, fn(x): x * 2)
expect(result).to_equal(10)
```

</details>

#### propagates nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_map(nil, fn(x): x * 2)
expect(result).to_be_nil()
```

</details>

### result_and_then

#### chains success

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_and_then(5, fn(x): x + 10)
expect(result).to_equal(15)
```

</details>

#### propagates nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_and_then(nil, fn(x): x + 10)
expect(result).to_be_nil()
```

</details>

### result_map_err

#### maps nil to new value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_map_err(nil, fn(): "error occurred")
expect(result).to_equal("error occurred")
```

</details>

#### passes through ok value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_map_err(42, fn(): "error occurred")
expect(result).to_equal(42)
```

</details>

### result_or_else

#### returns original when ok

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_or_else(42, fn(): 99)
expect(result).to_equal(42)
```

</details>

#### calls alternative when nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_or_else(nil, fn(): 99)
expect(result).to_equal(99)
```

</details>

### result_from_option

#### returns value when some

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_from_option(42, "no value")
expect(result).to_equal(42)
```

</details>

#### returns nil when nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = result_from_option(nil, "no value")
expect(result).to_be_nil()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/result_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Result stdlib
- result_is_ok and result_is_err
- result_unwrap_or
- result_map
- result_and_then
- result_map_err
- result_or_else
- result_from_option

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
