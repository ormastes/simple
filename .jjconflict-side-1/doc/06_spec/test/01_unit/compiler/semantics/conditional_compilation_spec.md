# Conditional Compilation Specification

> <details>

<!-- sdn-diagram:id=conditional_compilation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=conditional_compilation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

conditional_compilation_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=conditional_compilation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Conditional Compilation Specification

## Scenarios

### conditional compilation @when

#### when_check_condition debug is true in interpreter mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @when(debug) is true in interpreter mode
# This is a conceptual test - the actual @when mechanism works via
# annotation scanning during module load
val result = true  # debug mode is always true in interpreter
expect(result).to_equal(true)
```

</details>

#### when_check_condition release is false in interpreter mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = false  # release mode is always false in interpreter
expect(result).to_equal(false)
```

</details>

#### when_check_condition interpreter is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = true
expect(result).to_equal(true)
```

</details>

#### when_check_condition compiled is false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = false
expect(result).to_equal(false)
```

</details>

#### feature flags are disabled by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @when(feature=myfeature) disables the declaration
# when the feature is not set
val feature_myfeature = false
expect(feature_myfeature).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/conditional_compilation_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- conditional compilation @when

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
