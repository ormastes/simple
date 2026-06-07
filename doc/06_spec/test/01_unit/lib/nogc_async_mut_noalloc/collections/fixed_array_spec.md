# Fixed Array Specification

> <details>

<!-- sdn-diagram:id=fixed_array_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fixed_array_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fixed_array_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fixed_array_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fixed Array Specification

## Scenarios

### Fixed Array

#### keeps fixed capacity array operations available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = fixed_array_source()

expect(source).to_contain("class FixedArray:")
expect(source).to_contain("static fn new(capacity: i32) -> FixedArray")
expect(source).to_contain("me push(value: i64) -> bool")
expect(source).to_contain("fn get(index: i32) -> i64")
expect(source).to_contain("me set(index: i32, value: i64)")
expect(source).to_contain("me remove(index: i32) -> i64")
```

</details>

#### keeps fixed array state queries and factories available

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = fixed_array_source()

expect(source).to_contain("fn is_full() -> bool")
expect(source).to_contain("fn is_empty() -> bool")
expect(source).to_contain("fn size() -> i32")
expect(source).to_contain("fn contains(value: i64) -> bool")
expect(source).to_contain("fn index_of(value: i64) -> i32")
expect(source).to_contain("fn fixed_array_256() -> FixedArray")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_array_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Fixed Array

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
