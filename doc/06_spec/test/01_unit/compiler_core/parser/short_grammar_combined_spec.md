# Short Grammar Combined Specification

> <details>

<!-- sdn-diagram:id=short_grammar_combined_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=short_grammar_combined_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

short_grammar_combined_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=short_grammar_combined_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Short Grammar Combined Specification

## Scenarios

### Short grammar combined

#### pipe into composed function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = double >> add1
val result = 3 |> f
expect(result).to_equal(7)
```

</details>

#### comprehension piped to function

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nums = [for i in 0..5: i * i]
expect(nums).to_equal([0, 1, 4, 9, 16])
```

</details>

#### pipe chain with multiple functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 2 |> double |> triple |> add1
expect(result).to_equal(13)
```

</details>

#### compose chain then pipe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val transform = add1 >> double >> triple
val result = 1 |> transform
expect(result).to_equal(12)
```

</details>

#### comprehension with filter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evens = [for x in [1, 2, 3, 4, 5, 6] if x % 2 == 0: x * 10]
expect(evens).to_equal([20, 40, 60])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/parser/short_grammar_combined_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Short grammar combined

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
