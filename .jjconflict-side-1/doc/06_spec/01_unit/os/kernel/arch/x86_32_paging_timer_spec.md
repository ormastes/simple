# X86 32 Paging Timer Specification

> _Verifies hosted-safe x86_32 HAL geometry and timer state contracts._

<!-- sdn-diagram:id=x86_32_paging_timer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_32_paging_timer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_32_paging_timer_spec -> std
x86_32_paging_timer_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_32_paging_timer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 32 Paging Timer Specification

## Scenarios

### x86_32 paging and timer HAL parity
_Verifies hosted-safe x86_32 HAL geometry and timer state contracts._

#### exposes x86_32 paging geometry through the aggregate HAL

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hal = create_x86_32_hal()

expect(hal.paging.page_size()).to_equal(4096)
expect(hal.paging.address_levels()).to_equal(2)
```

</details>

#### exposes x86_32 paging geometry through the adapter aggregate

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val adapter = create_x86_32_hal_adapter()

expect(adapter.paging.page_size()).to_equal(4096)
expect(adapter.paging.address_levels()).to_equal(2)
```

</details>

#### exposes hosted-safe timer defaults through the aggregate HAL

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hal = create_x86_32_hal()

expect(hal.timer.frequency()).to_equal(0)
expect(hal.timer.ticks_per_second()).to_equal(0)
expect(hal.timer.elapsed_us()).to_equal(0)
```

</details>

#### routes timer tick state through HAL and adapter wrappers

1. pit tick handler
2. pit tick handler
   - Expected: hal.timer.current_ticks() equals `before + 2`
   - Expected: timer_current_ticks() equals `before + 2`
   - Expected: timer_frequency() equals `0`
   - Expected: timer_ticks_per_second() equals `0`
   - Expected: timer_elapsed_us() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = timer_current_ticks()
pit_tick_handler()
pit_tick_handler()

val hal = create_x86_32_hal()
expect(hal.timer.current_ticks()).to_equal(before + 2)
expect(timer_current_ticks()).to_equal(before + 2)
expect(timer_frequency()).to_equal(0)
expect(timer_ticks_per_second()).to_equal(0)
expect(timer_elapsed_us()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/x86_32_paging_timer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86_32 paging and timer HAL parity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
