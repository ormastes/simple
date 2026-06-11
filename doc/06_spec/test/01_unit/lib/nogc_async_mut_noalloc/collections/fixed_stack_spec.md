# Fixed Stack Specification

> <details>

<!-- sdn-diagram:id=fixed_stack_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fixed_stack_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fixed_stack_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fixed_stack_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fixed Stack Specification

## Scenarios

### Fixed Stack

#### keeps fixed capacity stack operations available

<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = fixed_stack_source()

expect(source).to_contain("class FixedStack:")
expect(source).to_contain("static fn new(capacity: i32) -> FixedStack")
expect(source).to_contain("me push(value: i64) -> bool")
expect(source).to_contain("me pop() -> i64")
expect(source).to_contain("fn peek() -> i64")
expect(source).to_contain("fn is_empty() -> bool")
expect(source).to_contain("fn is_full() -> bool")
expect(source).to_contain("fn depth() -> i32")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut_noalloc/collections/fixed_stack_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Fixed Stack

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
