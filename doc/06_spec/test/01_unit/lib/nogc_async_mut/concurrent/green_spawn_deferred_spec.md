# Green Spawn Deferred Specification

> <details>

<!-- sdn-diagram:id=green_spawn_deferred_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=green_spawn_deferred_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

green_spawn_deferred_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=green_spawn_deferred_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Green Spawn Deferred Specification

## Scenarios

### green_spawn deferred execution (E6)

#### spawn does not execute the body immediately

- assert true
- green run all


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
DEFERRED_COUNTER = 0
val before_counter = DEFERRED_COUNTER
val handle = green_spawn(deferred_body_inc)
val after_spawn_counter = DEFERRED_COUNTER
# Body must not have run yet
expect(before_counter).to_equal(0)
expect(after_spawn_counter).to_equal(0)
# Queue has one pending task
val ready = green_ready_count()
assert_true(ready >= 1)
# Clean up
green_run_all()
```

</details>

#### run_one executes the deferred body and marks handle done

- expect not
   - Expected: DEFERRED_COUNTER equals `0`
- assert true
   - Expected: DEFERRED_COUNTER equals `1`
- assert true
   - Expected: handle.join() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
DEFERRED_COUNTER = 0
val handle = green_spawn(deferred_body_inc)
expect_not(handle.is_done())
expect(DEFERRED_COUNTER).to_equal(0)
val ran = green_run_one()
assert_true(ran)
expect(DEFERRED_COUNTER).to_equal(1)
assert_true(handle.is_done())
expect(handle.join()).to_equal(1)
```

</details>

#### all deferred tasks execute on run_all and counter reaches N

- assert true
   - Expected: DEFERRED_COUNTER equals `3`
- assert true
- assert true
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
DEFERRED_COUNTER = 0
val h1 = green_spawn(deferred_body_inc)
val h2 = green_spawn(deferred_body_inc)
val h3 = green_spawn(deferred_body_inc)
# None have run yet
expect(DEFERRED_COUNTER).to_equal(0)
val ran = green_run_all()
assert_true(ran >= 3)
expect(DEFERRED_COUNTER).to_equal(3)
assert_true(h1.is_done())
assert_true(h2.is_done())
assert_true(h3.is_done())
```

</details>

#### a task with bad result does not stop sibling tasks

- green run all
   - Expected: SIBLING_RAN equals `2`
- assert true
- assert true
   - Expected: h_sibling1.join() equals `77`
   - Expected: h_sibling2.join() equals `77`
- assert true
   - Expected: bad_result equals `-99`
   - Expected: err_reason equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
SIBLING_RAN = 0
val h_bad = green_spawn(bad_result_body)
val h_sibling1 = green_spawn(sibling_body)
val h_sibling2 = green_spawn(sibling_body)
# None have run yet
expect(SIBLING_RAN).to_equal(0)
green_run_all()
# Siblings must have run despite bad_result_body
expect(SIBLING_RAN).to_equal(2)
assert_true(h_sibling1.is_done())
assert_true(h_sibling2.is_done())
expect(h_sibling1.join()).to_equal(77)
expect(h_sibling2.join()).to_equal(77)
# bad task is also done, result is the sentinel
assert_true(h_bad.is_done())
val bad_result = h_bad.join()
expect(bad_result).to_equal(-99)
# green_task_error returns empty for non-fatal value-level "error"
val err_reason = green_task_error(h_bad.id())
expect(err_reason).to_equal("")
```

</details>

#### green_spawn_value still works alongside deferred tasks

- expect not
- expect not
- green run all
- assert true
- assert true
   - Expected: h_value.join() equals `55`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h_value = green_spawn_value(55)
val h_deferred = green_spawn(deferred_body_inc)
expect_not(h_value.is_done())
expect_not(h_deferred.is_done())
green_run_all()
assert_true(h_value.is_done())
assert_true(h_deferred.is_done())
expect(h_value.join()).to_equal(55)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/concurrent/green_spawn_deferred_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- green_spawn deferred execution (E6)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
