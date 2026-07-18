# macro_consteval_simple_spec

> Simplified const-eval engine specification.

<!-- sdn-diagram:id=macro_consteval_simple_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_consteval_simple_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_consteval_simple_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_consteval_simple_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macro_consteval_simple_spec

Simplified const-eval engine specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/macro_consteval_simple_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Simplified const-eval engine specification.

Tests basic compile-time evaluation scenarios including arithmetic operations,
conditional expressions, loop evaluation, and string template processing.

## Scenarios

### Const-Eval Engine

### Arithmetic

#### evaluates expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simple_add!(20, 22)).to_equal(42)
```

</details>

#### evaluates multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simple_mul!(6, 7)).to_equal(42)
```

</details>

### Conditionals

#### evaluates max

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simple_max!(10, 50)).to_equal(50)
expect(simple_max!(100, 5)).to_equal(100)
```

</details>

#### evaluates min

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simple_min!(10, 50)).to_equal(10)
```

</details>

### Loops

#### sums ranges

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0 + 1 + 2 + 3 = 6
expect(simple_sum_range!(4)).to_equal(6)
```

</details>

#### generates indexed functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simple_idx_0() + simple_idx_1()).to_equal(1)
```

</details>

### Strings

#### concatenates in template

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(simple_get_test()).to_equal(42)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
