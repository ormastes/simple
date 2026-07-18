# X86 64 Hal Specification

> _Verifies the aggregate wires safe CPU and paging contracts._

<!-- sdn-diagram:id=x86_64_hal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_64_hal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_64_hal_spec -> std
x86_64_hal_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_64_hal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 64 Hal Specification

## Scenarios

### x86_64 HAL aggregate
_Verifies the aggregate wires safe CPU and paging contracts._

#### exposes x86_64 CPU identity metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hal = create_x86_64_hal()

expect(hal.cpu.cpu_id()).to_equal(0)
expect(hal.cpu.cpu_address_width()).to_equal(64)
```

</details>

#### exposes x86_64 paging geometry

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hal = create_x86_64_hal()

expect(hal.paging.page_size()).to_equal(4096)
expect(hal.paging.address_levels()).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/x86_64_hal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86_64 HAL aggregate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
