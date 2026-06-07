# Generator Specification

> <details>

<!-- sdn-diagram:id=generator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=generator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

generator_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=generator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generator Specification

## Scenarios

### Generator

#### defines generator protocol imports and constructors

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/nogc_async_mut/generator.spl")

expect(src.len()).to_be_greater_than(100)
expect(src).to_contain("iter_from_function")
expect(src).to_contain("iter_take")
expect(src).to_contain("iter_collect")
expect(src).to_contain("generate_range")
expect(src).to_contain("generate_repeat")
expect(src).to_contain("generator_from_coroutine")
expect(src).to_contain("coroutine")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/generator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Generator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
