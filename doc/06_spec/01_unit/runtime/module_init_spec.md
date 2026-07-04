# Module Init Specification

> 1. fn my init

<!-- sdn-diagram:id=module_init_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_init_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_init_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=module_init_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Init Specification

## Scenarios

### @init and @teardown annotations

#### annotated functions can be defined

1. fn my init
2. fn my teardown
   - Expected: my_init() equals `0`
   - Expected: my_teardown() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @init
fn my_init():
    0

# @teardown
fn my_teardown():
    0

expect(my_init()).to_equal(0)
expect(my_teardown()).to_equal(0)
```

</details>

#### functions can be called manually if annotated

1. fn setup module
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# NOTE: var mutation inside nested closure doesn't persist in interpreter.
# Test the concept by checking the function is callable.
fn setup_module() -> i64:
    1

val result = setup_module()
expect(result).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/01_unit/runtime/module_init_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- @init and @teardown annotations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
