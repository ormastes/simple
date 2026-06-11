# Tsan Facade Specification

> 1. tsan reset

<!-- sdn-diagram:id=tsan_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tsan_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tsan_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tsan_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tsan Facade Specification

## Scenarios

### nogc_async_mut sanitizer tsan facade

#### re-exports thread sanitizer race checks and records

1. tsan reset
   - Expected: tsan_is_enabled() is false
2. tsan set thread
3. tsan write
   - Expected: tsan_error_count() equals `0`
4. tsan enable
   - Expected: tsan_is_enabled() is true
5. tsan write
6. tsan set thread
7. tsan read
   - Expected: tsan_error_count() equals `1`
   - Expected: tsan_get_events()[0].kind equals `tsan`
   - Expected: race.var_id equals `counter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
tsan_reset()
expect(tsan_is_enabled()).to_equal(false)
tsan_set_thread(1)
tsan_write("counter", "disabled")
expect(tsan_error_count()).to_equal(0)

tsan_enable()
expect(tsan_is_enabled()).to_equal(true)
tsan_write("counter", "main.spl:10")
tsan_set_thread(2)
tsan_read("counter", "worker.spl:20")
expect(tsan_error_count()).to_equal(1)
expect(tsan_get_events()[0].kind).to_equal("tsan")

val race = data_race("counter", 1, 2, "worker.spl:20")
expect(race.var_id).to_equal("counter")
```

</details>

#### re-exports lock order checks

1. tsan reset
2. tsan enable
3. tsan set thread
4. tsan lock acquire
5. tsan lock acquire
6. tsan set thread
7. tsan lock acquire
8. tsan lock acquire
   - Expected: tsan_error_count() equals `1`
   - Expected: tsan_get_events()[0].kind equals `tsan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
tsan_reset()
tsan_enable()
tsan_set_thread(1)
tsan_lock_acquire("a")
tsan_lock_acquire("b")
tsan_set_thread(2)
tsan_lock_acquire("b")
tsan_lock_acquire("a")
expect(tsan_error_count()).to_equal(1)
expect(tsan_get_events()[0].kind).to_equal("tsan")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/sanitizer/tsan/tsan_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut sanitizer tsan facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
