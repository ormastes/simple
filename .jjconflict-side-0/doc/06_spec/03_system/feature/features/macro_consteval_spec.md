# macro_consteval_spec

> Const-eval engine specification.

<!-- sdn-diagram:id=macro_consteval_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_consteval_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_consteval_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_consteval_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macro_consteval_spec

Const-eval engine specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/macro_consteval_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Const-eval engine specification.

Tests the compile-time evaluation engine for macros including arithmetic
evaluation, conditional expressions, and loop-based code generation.

## Scenarios

### Const-Eval Engine

### Arithmetic evaluation

#### evaluates addition and multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = ce_compute!(10, 16)
# 10 + 16 * 2 = 10 + 32 = 42
expect(x).to_equal(42)
```

</details>

#### evaluates with zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = ce_with_zero!(42)
expect(x).to_equal(42)
```

</details>

#### evaluates subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = ce_subtract!(50, 8)
expect(x).to_equal(42)
```

</details>

### Conditional evaluation

#### evaluates max correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_max!(10, 50)).to_equal(50)
expect(ce_max!(100, 5)).to_equal(100)
expect(ce_max!(42, 42)).to_equal(42)
```

</details>

#### evaluates min correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_min!(10, 50)).to_equal(10)
expect(ce_min!(100, 5)).to_equal(5)
```

</details>

#### evaluates abs correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ce_abs!(42)).to_equal(42)
expect(ce_abs!(-42)).to_equal(42)
expect(ce_abs!(0)).to_equal(0)
```

</details>

### Loop evaluation

<details>
<summary>Advanced: generates functions with for loop</summary>

#### generates functions with for loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sum = ce_loop_get_0() + ce_loop_get_1() + ce_loop_get_2()
expect(sum).to_equal(3)
```

</details>


</details>

#### handles range iteration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# 0 + 1 + 2 + 3 + 4 = 10
val x = ce_sum_range!(5)
expect(x).to_equal(10)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
