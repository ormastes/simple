# Spec Framework Specification

> <details>

<!-- sdn-diagram:id=spec_framework_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=spec_framework_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

spec_framework_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=spec_framework_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Spec Framework Specification

## Scenarios

### SPipe Framework

#### describe and context nesting

#### runs basic test

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1 + 1).to_equal(2)
```

</details>

#### supports nested context

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context_name = "describe/context nesting"
expect(context_name).to_contain("context")
```

</details>

#### expect() matchers

#### to_equal checks equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(42).to_equal(42)
expect("hello").to_equal("hello")
```

</details>

#### to_be is alias for to_equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(10).to_be(10)
```

</details>

#### to_equal true checks boolean true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enabled = true
expect(enabled).to_equal(not false)
```

</details>

#### to_equal false checks boolean false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(false).to_equal(false)
```

</details>

#### to_be_nil checks nil

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(nil).to_be_nil()
```

</details>

#### to_contain checks string membership

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("hello world").to_contain("world")
```

</details>

#### to_contain checks array membership

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect([1, 2, 3]).to_contain(2)
```

</details>

#### to_start_with checks prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("hello").to_start_with("hel")
```

</details>

#### to_end_with checks suffix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("hello").to_end_with("llo")
```

</details>

#### to_be_greater_than compares

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(10).to_be_greater_than(5)
```

</details>

#### to_be_less_than compares

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(5).to_be_less_than(10)
```

</details>

#### value comparisons

#### equality with strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect("abc").to_equal("abc")
```

</details>

#### equality with arrays

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect([1, 2]).to_equal([1, 2])
```

</details>

#### nil equality

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(nil).to_be_nil()
expect(nil).to_equal(nil)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/spec_framework_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SPipe Framework

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
