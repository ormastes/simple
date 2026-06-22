# Shared Dataset Specification

> 1. shared dataset init

<!-- sdn-diagram:id=shared_dataset_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=shared_dataset_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

shared_dataset_spec -> std
shared_dataset_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=shared_dataset_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared Dataset Specification

## Scenarios

### kernel shared dataset manager

#### creates handle zero as a valid dataset

1. shared dataset init
   - Expected: handle equals `0`
   - Expected: shared_dataset_size(handle as u64) equals `8`
   - Expected: shared_dataset_is_sealed(handle as u64) is false
   - Expected: shared_dataset_handle_slot(handle as u64) equals `0`
   - Expected: shared_dataset_handle_generation(handle as u64) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_dataset_init()

val handle = shared_dataset_create(8, 0)

expect(handle).to_equal(0)
expect(shared_dataset_size(handle as u64)).to_equal(8)
expect(shared_dataset_is_sealed(handle as u64)).to_equal(false)
expect(shared_dataset_handle_slot(handle as u64)).to_equal(0)
expect(shared_dataset_handle_generation(handle as u64)).to_equal(0)
```

</details>

#### writes before seal and reads after seal

1. shared dataset init
   - Expected: shared_dataset_write(handle as u64, 0, [10u8, 20u8]) equals `2`
   - Expected: shared_dataset_write_byte(handle as u64, 2, 30u8) equals `1`
   - Expected: shared_dataset_write_byte(handle as u64, 3, 40u8) equals `1`
   - Expected: shared_dataset_seal(handle as u64) equals `0`
   - Expected: read.status equals `4`
   - Expected: read.len equals `4`
   - Expected: read.data[0] equals `10u8`
   - Expected: read.data[1] equals `20u8`
   - Expected: read.data[2] equals `30u8`
   - Expected: read.data[3] equals `40u8`
   - Expected: shared_dataset_read_byte(handle as u64, 2) equals `30`
   - Expected: shared_dataset_flags(handle as u64) equals `7`
   - Expected: shared_dataset_is_sealed(handle as u64) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_dataset_init()
val handle = shared_dataset_create(4, 7)

expect(shared_dataset_write(handle as u64, 0, [10u8, 20u8])).to_equal(2)
expect(shared_dataset_write_byte(handle as u64, 2, 30u8)).to_equal(1)
expect(shared_dataset_write_byte(handle as u64, 3, 40u8)).to_equal(1)
expect(shared_dataset_seal(handle as u64)).to_equal(0)

val read = shared_dataset_read(handle as u64, 0, 4)
expect(read.status).to_equal(4)
expect(read.len).to_equal(4)
expect(read.data[0]).to_equal(10u8)
expect(read.data[1]).to_equal(20u8)
expect(read.data[2]).to_equal(30u8)
expect(read.data[3]).to_equal(40u8)
expect(shared_dataset_read_byte(handle as u64, 2)).to_equal(30)
expect(shared_dataset_flags(handle as u64)).to_equal(7)
expect(shared_dataset_is_sealed(handle as u64)).to_equal(true)
```

</details>

#### rejects reads before seal and writes after seal

1. shared dataset init
   - Expected: shared_dataset_write(handle as u64, 0, [1u8, 2u8]) equals `2`
   - Expected: shared_dataset_read_byte(handle as u64, 0) equals `0 - EINVAL as i64`
   - Expected: shared_dataset_seal(handle as u64) equals `0`
   - Expected: shared_dataset_write(handle as u64, 0, [3u8]) equals `0 - EINVAL as i64`
   - Expected: shared_dataset_write_byte(handle as u64, 1, 4u8) equals `0 - EINVAL as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_dataset_init()
val handle = shared_dataset_create(2, 0)

expect(shared_dataset_write(handle as u64, 0, [1u8, 2u8])).to_equal(2)
expect(shared_dataset_read_byte(handle as u64, 0)).to_equal(0 - EINVAL as i64)
expect(shared_dataset_seal(handle as u64)).to_equal(0)
expect(shared_dataset_write(handle as u64, 0, [3u8])).to_equal(0 - EINVAL as i64)
expect(shared_dataset_write_byte(handle as u64, 1, 4u8)).to_equal(0 - EINVAL as i64)
```

</details>

#### rejects invalid size handle and range inputs

1. shared dataset init
   - Expected: shared_dataset_create(0, 0) equals `0 - EINVAL as i64`
   - Expected: shared_dataset_create(4097, 0) equals `0 - EINVAL as i64`
   - Expected: shared_dataset_size(SHARED_DATASET_INVALID_HANDLE) equals `0 - EBADF as i64`
   - Expected: shared_dataset_write(SHARED_DATASET_INVALID_HANDLE, 0, [1u8]) equals `0 - EBADF as i64`
   - Expected: shared_dataset_write(handle as u64, 3, [1u8]) equals `0 - EINVAL as i64`
   - Expected: shared_dataset_write_byte(handle as u64, 3, 1u8) equals `0 - EINVAL as i64`
   - Expected: shared_dataset_seal(handle as u64) equals `0`
   - Expected: shared_dataset_read(handle as u64, 2, 2).status equals `0 - EINVAL as i64`
   - Expected: shared_dataset_read_byte(handle as u64, 3) equals `0 - EINVAL as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_dataset_init()

expect(shared_dataset_create(0, 0)).to_equal(0 - EINVAL as i64)
expect(shared_dataset_create(4097, 0)).to_equal(0 - EINVAL as i64)
expect(shared_dataset_size(SHARED_DATASET_INVALID_HANDLE)).to_equal(0 - EBADF as i64)
expect(shared_dataset_write(SHARED_DATASET_INVALID_HANDLE, 0, [1u8])).to_equal(0 - EBADF as i64)

val handle = shared_dataset_create(3, 0)
expect(shared_dataset_write(handle as u64, 3, [1u8])).to_equal(0 - EINVAL as i64)
expect(shared_dataset_write_byte(handle as u64, 3, 1u8)).to_equal(0 - EINVAL as i64)
expect(shared_dataset_seal(handle as u64)).to_equal(0)
expect(shared_dataset_read(handle as u64, 2, 2).status).to_equal(0 - EINVAL as i64)
expect(shared_dataset_read_byte(handle as u64, 3)).to_equal(0 - EINVAL as i64)
```

</details>

#### closes frees slot and invalidates the old generation

1. shared dataset init
   - Expected: first equals `0`
   - Expected: shared_dataset_write(first as u64, 0, [8u8, 9u8]) equals `2`
   - Expected: shared_dataset_seal(first as u64) equals `0`
   - Expected: shared_dataset_close(first as u64) equals `0`
   - Expected: shared_dataset_size(first as u64) equals `0 - EBADF as i64`
   - Expected: shared_dataset_close(first as u64) equals `0 - EBADF as i64`
   - Expected: shared_dataset_handle_slot(second as u64) equals `0`
   - Expected: shared_dataset_handle_generation(second as u64) equals `1`
   - Expected: second equals `65536`
   - Expected: shared_dataset_read_byte(first as u64, 0) equals `0 - EBADF as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_dataset_init()

val first = shared_dataset_create(2, 0)
expect(first).to_equal(0)
expect(shared_dataset_write(first as u64, 0, [8u8, 9u8])).to_equal(2)
expect(shared_dataset_seal(first as u64)).to_equal(0)
expect(shared_dataset_close(first as u64)).to_equal(0)

expect(shared_dataset_size(first as u64)).to_equal(0 - EBADF as i64)
expect(shared_dataset_close(first as u64)).to_equal(0 - EBADF as i64)

val second = shared_dataset_create(2, 0)
expect(shared_dataset_handle_slot(second as u64)).to_equal(0)
expect(shared_dataset_handle_generation(second as u64)).to_equal(1)
expect(second).to_equal(65536)
expect(shared_dataset_read_byte(first as u64, 0)).to_equal(0 - EBADF as i64)
```

</details>

#### allows closing unsealed builders

1. shared dataset init
   - Expected: shared_dataset_close(handle as u64) equals `0`
   - Expected: shared_dataset_write_byte(handle as u64, 0, 1u8) equals `0 - EBADF as i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shared_dataset_init()

val handle = shared_dataset_create(1, 0)

expect(shared_dataset_close(handle as u64)).to_equal(0)
expect(shared_dataset_write_byte(handle as u64, 0, 1u8)).to_equal(0 - EBADF as i64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/shared_dataset_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- kernel shared dataset manager

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
