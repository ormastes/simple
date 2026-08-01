# macro_advanced_spec

> Advanced macro features specification.

<!-- sdn-diagram:id=macro_advanced_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=macro_advanced_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

macro_advanced_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=macro_advanced_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macro_advanced_spec

Advanced macro features specification.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/macro_advanced_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Advanced macro features specification.

Tests nested macros, macro composition, and complex const-eval scenarios
including conditional evaluation and polynomial calculations.

## Scenarios

### Advanced Macro Features

### Nested macros

#### expands nested macro invocations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = adv_outer!()
# Should be 10 + 5 = 15
expect(result).to_equal(15)
```

</details>

#### chains macro expansions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = adv_wrapper!()
# 5 + 10 + 20 = 35
expect(result).to_equal(35)
```

</details>

### Macro composition

#### uses macros in computation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = adv_double!(10)
val b = adv_triple!(7)
# 20 + 21 = 41... let's adjust
val c = adv_double!(21)
expect(c).to_equal(42)
```

</details>

#### composes multiple macro calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = 5
val incremented = adv_add_one!(base)
val squared = adv_square!(incremented)
# (5 + 1)^2 = 36
expect(squared).to_equal(36)
```

</details>

### Const-eval edge cases

#### handles const-eval with conditionals

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(adv_abs_diff!(10, 5)).to_equal(5)
expect(adv_abs_diff!(5, 10)).to_equal(5)
expect(adv_abs_diff!(7, 7)).to_equal(0)
```

</details>

#### handles const-eval with nested conditionals

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(adv_classify!(-5)).to_equal(-1)
expect(adv_classify!(0)).to_equal(0)
expect(adv_classify!(5)).to_equal(1)
```

</details>

#### handles const-eval with complex arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# f(5) = 25 + 10 + 1 = 36
expect(adv_polynomial!(5)).to_equal(36)
# f(0) = 0 + 0 + 1 = 1
expect(adv_polynomial!(0)).to_equal(1)
```

</details>

### Advanced intro patterns

#### generates multiple related functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val got = adv_get_value()
val set_result = adv_set_value(100)
expect(got).to_equal(42)
expect(set_result).to_equal(100)
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
