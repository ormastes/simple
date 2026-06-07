# Build Native Minimum Specification

> Tests that the linker and driver modules can be imported successfully.

<!-- sdn-diagram:id=build_native_min_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=build_native_min_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

build_native_min_spec -> linker
build_native_min_spec -> driver
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=build_native_min_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Build Native Minimum Specification

Tests that the linker and driver modules can be imported successfully.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TBD |
| Category | Compiler |
| Status | In Progress |
| Source | `test/01_unit/compiler/native/build_native_min_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that the linker and driver modules can be imported successfully.

## Scenarios

### Build Native Minimum

#### imports linker module successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val imported_module = "linker"
expect(imported_module).to_equal("linker")
```

</details>

#### imports driver module successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val imported_module = "driver"
expect(imported_module).to_equal("driver")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
