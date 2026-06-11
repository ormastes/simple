# Lazy Val Specification

> <details>

<!-- sdn-diagram:id=lazy_val_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lazy_val_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lazy_val_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lazy_val_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lazy Val Specification

## Scenarios

### lazy val declarations

#### lazy thunk at module level is evaluatable

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(expensive_result()).to_equal(42000)
```

</details>

#### lazy string concatenation works

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(lazy_string()).to_equal("hello world")
```

</details>

#### lazy val in function body via thunk

1. fn compute
2. thunk
   - Expected: r equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn compute():
    val thunk = fn(): 10 + 20
    thunk()
val r = compute()
expect(r).to_equal(30)
```

</details>

#### lazy val with complex expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val thunk = fn(): 5 * 5 + 3
val n = thunk()
expect(n).to_equal(28)
```

</details>

#### make_thunk wraps a thunk

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val orig = fn(): 99
val wrapped = make_thunk(orig)
expect(wrapped()).to_equal(99)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/parser/lazy_val_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- lazy val declarations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
