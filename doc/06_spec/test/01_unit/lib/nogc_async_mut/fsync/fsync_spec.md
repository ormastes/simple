# Fsync Specification

> 1. fsync mutex lock

<!-- sdn-diagram:id=fsync_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fsync_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fsync_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fsync_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fsync Specification

## Scenarios

### fsync mutex/condvar

#### lock and unlock on address 0 complete without error

1. fsync mutex lock
2. fsync mutex unlock
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr: u32 = 0
fsync_mutex_lock(addr)
fsync_mutex_unlock(addr)
expect(1).to_equal(1)
```

</details>

#### lock and unlock on non-zero address complete without error

1. fsync mutex lock
2. fsync mutex unlock
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val addr: u32 = 42
fsync_mutex_lock(addr)
fsync_mutex_unlock(addr)
expect(1).to_equal(1)
```

</details>

#### multiple lock/unlock pairs on different addresses do not interfere

1. fsync mutex lock
2. fsync mutex lock
3. fsync mutex unlock
4. fsync mutex unlock
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a: u32 = 1
val b: u32 = 2
fsync_mutex_lock(a)
fsync_mutex_lock(b)
fsync_mutex_unlock(b)
fsync_mutex_unlock(a)
expect(1).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/fsync/fsync_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- fsync mutex/condvar

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
