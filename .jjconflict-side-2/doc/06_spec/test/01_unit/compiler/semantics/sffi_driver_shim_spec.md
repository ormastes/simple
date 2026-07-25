# Sffi Driver Shim Specification

> <details>

<!-- sdn-diagram:id=sffi_driver_shim_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sffi_driver_shim_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sffi_driver_shim_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sffi_driver_shim_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sffi Driver Shim Specification

## Scenarios

### SFFI007 driver shim conformance

#### errors when a @driver module has extern functions but no Driver impl

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = check_sffi007_driver_shim(true, true, false, "nvme", "nvme.spl")

expect(warnings.len()).to_equal(1)
expect(warnings[0].code).to_equal("SFFI007")
expect(warnings[0].severity).to_equal("ERROR")
expect(warnings[0].message).to_contain("no `impl Driver for X`")
```

</details>

#### passes when the @driver extern shim has a Driver impl

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = check_sffi007_driver_shim(true, true, true, "nvme", "nvme.spl")

expect(warnings.len()).to_equal(0)
```

</details>

#### ignores modules without extern driver shims

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(check_sffi007_driver_shim(false, true, false, "pure", "pure.spl").len()).to_equal(0)
expect(check_sffi007_driver_shim(true, false, false, "native", "native.spl").len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/semantics/sffi_driver_shim_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SFFI007 driver shim conformance

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
