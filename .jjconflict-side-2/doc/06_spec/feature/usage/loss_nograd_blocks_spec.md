# loss{} and nograd{} Block Tests

> Tests that `loss{}` and `nograd{}` blocks parse, evaluate, and render the same supported math-expression subset as `m{}` blocks. Runtime autograd semantics are covered by `math_autograd_runtime_spec.spl`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# loss{} and nograd{} Block Tests

Tests that `loss{}` and `nograd{}` blocks parse, evaluate, and render the same supported math-expression subset as `m{}` blocks. Runtime autograd semantics are covered by `math_autograd_runtime_spec.spl`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #1099-1102 (loss/nograd block support) |
| Category | Syntax / Math DSL |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/feature/usage/loss_nograd_blocks_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that `loss{}` and `nograd{}` blocks parse, evaluate, and render the
same supported math-expression subset as `m{}` blocks. Runtime autograd
semantics are covered by `math_autograd_runtime_spec.spl`.

## Scenarios

### loss{} block evaluation

#### basic arithmetic

#### evaluates addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = loss{ 2 + 3 }
expect(result).to_equal(5)
```

</details>

#### evaluates subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = loss{ 10 - 4 }
expect(result).to_equal(6)
```

</details>

#### evaluates multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = loss{ 3 * 4 }
expect(result).to_equal(12)
```

</details>

#### evaluates division

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = loss{ 10 / 2 }
expect(result).to_equal(5)
```

</details>

#### power operator

#### evaluates integer power

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3.0
val result = loss{ x^2 }
expect(result).to_equal(9.0)
```

</details>

#### evaluates fractional power

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 4.0
val result = loss{ x^0.5 }
expect(result).to_equal(2.0)
```

</details>

#### fractions

#### evaluates frac

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = loss{ frac(1, 2) }
expect(result).to_equal(0.5)
```

</details>

#### evaluates nested frac

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = loss{ frac(1, frac(1, 2)) }
expect(result).to_equal(2.0)
```

</details>

#### scope variable bridging

#### reads outer variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5.0
val y = 3.0
val result = loss{ x + y }
expect(result).to_equal(8.0)
```

</details>

#### reads multiple outer variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 2.0
val b = 3.0
val c = 4.0
val result = loss{ a * b + c }
expect(result).to_equal(10.0)
```

</details>

#### math functions

#### evaluates sqrt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = loss{ sqrt(16) }
expect(result).to_equal(4.0)
```

</details>

#### evaluates exp

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(close(loss{ exp(0) }, 1.0, 0.01)).to_equal(true)
```

</details>

#### evaluates abs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = loss{ abs(-5) }
expect(result).to_equal(5)
```

</details>

### nograd{} block evaluation

#### basic arithmetic

#### evaluates addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = nograd{ 2 + 3 }
expect(result).to_equal(5)
```

</details>

#### evaluates subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = nograd{ 10 - 4 }
expect(result).to_equal(6)
```

</details>

#### evaluates multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = nograd{ 3 * 4 }
expect(result).to_equal(12)
```

</details>

#### evaluates division

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = nograd{ 10 / 2 }
expect(result).to_equal(5)
```

</details>

#### power operator

#### evaluates integer power

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3.0
val result = nograd{ x^2 }
expect(result).to_equal(9.0)
```

</details>

#### evaluates fractional power

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 4.0
val result = nograd{ x^0.5 }
expect(result).to_equal(2.0)
```

</details>

#### fractions

#### evaluates frac

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = nograd{ frac(1, 2) }
expect(result).to_equal(0.5)
```

</details>

#### scope variable bridging

#### reads outer variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5.0
val y = 3.0
val result = nograd{ x + y }
expect(result).to_equal(8.0)
```

</details>

#### math functions

#### evaluates sqrt

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = nograd{ sqrt(16) }
expect(result).to_equal(4.0)
```

</details>

#### evaluates exp

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(close(nograd{ exp(0) }, 1.0, 0.01)).to_equal(true)
```

</details>

### loss{} rendering

#### renders LaTeX via render_latex_raw

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("frac(1, 1 + exp(-x))")
expect(latex).to_contain("\\frac")
expect(latex).to_contain("\\exp")
```

</details>

#### renders Unicode via to_pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("frac(1, 1 + exp(-x))")
expect(pretty).to_contain("exp")
```

</details>

### nograd{} rendering

#### renders LaTeX via render_latex_raw

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val latex = render_latex_raw("sqrt(frac(6, fan_in + fan_out))")
expect(latex).to_contain("\\sqrt")
expect(latex).to_contain("\\frac")
```

</details>

#### renders Unicode via to_pretty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pretty = to_pretty("sqrt(frac(6, fan_in + fan_out))")
expect(pretty).to_contain("√")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
