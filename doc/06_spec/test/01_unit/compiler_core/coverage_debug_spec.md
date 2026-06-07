# Coverage Debug Specification

> 1. check

<!-- sdn-diagram:id=coverage_debug_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=coverage_debug_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

coverage_debug_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=coverage_debug_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coverage Debug Specification

## Scenarios

### Coverage Instrumentation Test

#### simple if branch - true

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
if x > 5:
    check(true)
else:
    check(false)
```

</details>

#### simple if branch - false

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2
if x > 5:
    check(false)
else:
    check(true)
```

</details>

#### match statement

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1
val result = match x:
    1: "one"
    2: "two"
    _: "other"
check(result == "one")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/coverage_debug_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Coverage Instrumentation Test

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
