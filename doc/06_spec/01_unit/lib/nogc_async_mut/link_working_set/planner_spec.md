# Planner Specification

> Tests covering bounded linker working-set planner, bounded linker spill integrity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Planner Specification

## Scenarios

### bounded linker working-set planner

#### windows a large input beneath the resident limit

- Plan 20 GB of inputs with 512 MB input and output windows


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan 20 GB of inputs with 512 MB input and output windows")
val plan = plan_link_working_set_v1(20000000000, 512000000, 512000000, 256000000, 6000000000)
assert_equal(plan.status, LinkWorkingSetStatus.Ok)
assert_equal(plan.resident_bytes, 1280000000u64)
assert_equal(plan.window_count, 40u64)
assert_true(plan.spill_required)
```

</details>

#### rejects invalid, overflowing, and over-budget plans

- Exercise every fail-closed planning result


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise every fail-closed planning result")
assert_equal(plan_link_working_set_v1(1, 1, 1, 1, 0).status, LinkWorkingSetStatus.InvalidLimit)
assert_equal(plan_link_working_set_v1(1, 0, 1, 1, 10).status, LinkWorkingSetStatus.InvalidWindow)
assert_equal(plan_link_working_set_v1(1, 0xffffffffffffffffu64, 1, 0, 10).status, LinkWorkingSetStatus.ArithmeticOverflow)
assert_equal(plan_link_working_set_v1(10, 6, 6, 1, 12).status, LinkWorkingSetStatus.ResidentBudgetExceeded)
```

</details>

### bounded linker spill integrity

#### should reject a spill extent whose exclusive end overflows

- Place one byte at the maximum output offset


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Place one byte at the maximum output offset")
val frame = link_spill_frame_v1(0xffffffffffffffffu64, [1u8])
expect(link_spill_frame_v1_valid(frame, [1u8])).to_be(false)
```

</details>

#### should accept a spill extent ending at the maximum representable offset

- Place two bytes immediately before the maximum output offset


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Place two bytes immediately before the maximum output offset")
val frame = link_spill_frame_v1(0xfffffffffffffffdu64, [1u8, 2u8])
expect(link_spill_frame_v1_valid(frame, [1u8, 2u8])).to_be(true)
```

</details>

#### should accept an empty spill frame at the maximum offset

- Validate an empty frame at the output boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate an empty frame at the output boundary")
val frame = link_spill_frame_v1(0xffffffffffffffffu64, [])
expect(link_spill_frame_v1_valid(frame, [])).to_be(true)
```

</details>

#### detects payload corruption and truncation

- Checksum a staged output frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Checksum a staged output frame")
val frame = link_spill_frame_v1(4096, [1u8, 2u8, 3u8, 4u8])
assert_true(link_spill_frame_v1_valid(frame, [1u8, 2u8, 3u8, 4u8]))
assert_false(link_spill_frame_v1_valid(frame, [1u8, 2u8, 3u8, 5u8]))
assert_false(link_spill_frame_v1_valid(frame, [1u8, 2u8, 3u8]))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/link_working_set/planner_spec.spl` |
| Updated | 2026-09-29 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bounded linker working-set planner, bounded linker spill integrity.
- bounded linker working-set planner
- bounded linker spill integrity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
