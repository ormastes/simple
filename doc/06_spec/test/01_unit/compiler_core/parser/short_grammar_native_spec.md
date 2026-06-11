# Short Grammar Native Specification

> <details>

<!-- sdn-diagram:id=short_grammar_native_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=short_grammar_native_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

short_grammar_native_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=short_grammar_native_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Short Grammar Native Specification

## Scenarios

### Short grammar native

#### compiles expression-bodied functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(native_short_double(21)).to_equal(42)
```

</details>

#### compiles list comprehensions without pipe dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val squares = [for x in 0..5: x * x]
expect(squares).to_equal([0, 1, 4, 9, 16])
```

</details>

#### compiles filtered comprehensions without pipe dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evens = [for x in 0..7 if x % 2 == 0: x]
expect(evens).to_equal([0, 2, 4, 6])
```

</details>

#### compiles placeholders inside inline if expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = [1, 2, 3, 4].map(if _1 % 2 == 0: _1 * 10 else: 0)
expect(values).to_equal([0, 20, 0, 40])
```

</details>

#### compiles nil coalescing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val maybe: Option<i64> = nil
expect(maybe ?? 9).to_equal(9)
```

</details>

#### uses regular calls where native pipe is unavailable

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(native_short_add(native_short_double(3), 1)).to_equal(7)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/parser/short_grammar_native_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Short grammar native

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
