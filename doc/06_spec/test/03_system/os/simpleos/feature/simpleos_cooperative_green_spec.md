# SimpleOS Cooperative Green System Contract

> This system spec proves that the implemented cooperative-green API remains usable in the SimpleOS feature lane while preserving its explicit semantics: it queues logical work on the current carrier and does not claim CPU-parallel M:N execution.

<!-- sdn-diagram:id=simpleos_cooperative_green_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_cooperative_green_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_cooperative_green_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_cooperative_green_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Cooperative Green System Contract

This system spec proves that the implemented cooperative-green API remains usable in the SimpleOS feature lane while preserving its explicit semantics: it queues logical work on the current carrier and does not claim CPU-parallel M:N execution.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-simpleos-cooperative |
| Category | SimpleOS / Concurrency |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | N/A |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec proves that the implemented cooperative-green API remains
usable in the SimpleOS feature lane while preserving its explicit semantics: it
queues logical work on the current carrier and does not claim CPU-parallel M:N
execution.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** N/A

## Research

**Research:** doc/01_research/local/multicore_green.md

## Syntax

Run the hosted SimpleOS cooperative-green contract:

```sh
./src/compiler_rust/target/debug/simple test test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl --mode=interpreter --clean
```

## Examples

The scenarios prove that `cooperative_green_spawn` and
`cooperative_green_spawn_value` queue logical work on the current carrier,
remain pending before the carrier runs, and return their values after
`cooperative_green_run_one` or `cooperative_green_run_all`. This is current
carrier cooperative scheduling, not CPU-parallel M:N execution.

## Scenario Walkthrough

### Pending Until Carrier Run

1. Read the current cooperative ready queue depth.
2. Queue one logical green task with `cooperative_green_spawn`.
3. Assert the handle is not done before the carrier runs.
4. Assert the ready queue depth increased by one.
5. Run one cooperative carrier turn.
6. Assert the handle is done and joins to the expected value.

### Drain Current Carrier

1. Read the current cooperative ready queue depth.
2. Queue two logical green tasks.
3. Assert both tasks are visible in the ready queue.
4. Run all queued cooperative work on the current carrier.
5. Assert at least two tasks ran.
6. Join both handles and assert their expected values.

### Direct Value Scheduling

1. Queue a direct value with `cooperative_green_spawn_value`.
2. Assert the value handle remains pending before a carrier turn.
3. Run one cooperative carrier turn.
4. Join the value handle and assert the direct value is returned.

## Evidence Boundary

- This spec proves hosted SimpleOS compatibility for the cooperative-green
  public API.
- It intentionally does not claim multicore CPU parallelism.
- It keeps cooperative-green evidence separate from `multicore_green_spawn`
  and from OS-thread `thread_spawn` evidence.
- It is valid fast evidence for current-carrier logical scheduling.
- Go-like M:N claims require `multicore_green_spawn` runtime-pool evidence or
  SimpleOS scheduler/AP evidence, not this cooperative queue alone.

## Traceability Notes

- `cooperative_green_spawn` covers closure-style logical work.
- `cooperative_green_spawn_value` covers direct value fanout rows.
- `cooperative_green_ready_count` is used as queue-depth evidence.
- `cooperative_green_run_one` proves one carrier turn.
- `cooperative_green_run_all` proves queue draining.
- The checked values `3`, `8`, and `21` are stable sentinel results.
- This manual should stay aligned with the profile guide classification.
- If cooperative-green gains CPU-parallel behavior later, this spec and guide
  must be updated together.

## TUI Capture

```text
Simple Test Runner v1.0.0-beta
Running: test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl
[1/1] test/03_system/os/simpleos/feature/simpleos_cooperative_green_spec.spl PASSED
Files: 1
Passed: 3
Failed: 0
```

## Scenarios

### SimpleOS cooperative green contract

#### queues logical green work without marking it done before the carrier runs

1. Record the current SimpleOS cooperative carrier queue depth
2. Queue a logical green task on the current carrier
3. Verify the task is pending until the carrier runs
   - Expected: handle.is_done() is false
   - Expected: cooperative_green_ready_count() equals `before + 1`
4. Run one cooperative carrier turn
   - Expected: cooperative_green_run_one() is true
5. Verify the queued task completed with its expected value
   - Expected: handle.is_done() is true
   - Expected: handle.join() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record the current SimpleOS cooperative carrier queue depth")
val before = cooperative_green_ready_count()
step("Queue a logical green task on the current carrier")
val handle = cooperative_green_spawn(simpleos_cooperative_green_value_3)

step("Verify the task is pending until the carrier runs")
expect(handle.is_done()).to_equal(false)
expect(cooperative_green_ready_count()).to_equal(before + 1)
step("Run one cooperative carrier turn")
expect(cooperative_green_run_one()).to_equal(true)
step("Verify the queued task completed with its expected value")
expect(handle.is_done()).to_equal(true)
expect(handle.join()).to_equal(3)
```

</details>

#### runs all queued cooperative work on the current carrier

1. Record the current SimpleOS cooperative carrier queue depth
2. Queue two logical green tasks on the current carrier
3. Verify both tasks are visible in the ready queue
   - Expected: cooperative_green_ready_count() equals `before + 2`
4. Run the cooperative carrier until the queue is drained
5. Verify both queued tasks completed on the current carrier
   - Expected: ran >= 2 is true
   - Expected: h1.join() equals `3`
   - Expected: h2.join() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record the current SimpleOS cooperative carrier queue depth")
val before = cooperative_green_ready_count()
step("Queue two logical green tasks on the current carrier")
val h1 = cooperative_green_spawn(simpleos_cooperative_green_value_3)
val h2 = cooperative_green_spawn(simpleos_cooperative_green_value_8)

step("Verify both tasks are visible in the ready queue")
expect(cooperative_green_ready_count()).to_equal(before + 2)
step("Run the cooperative carrier until the queue is drained")
val ran = cooperative_green_run_all()

step("Verify both queued tasks completed on the current carrier")
expect(ran >= 2).to_equal(true)
expect(h1.join()).to_equal(3)
expect(h2.join()).to_equal(8)
```

</details>

#### supports direct value scheduling used by profile fanout rows

1. Record the current SimpleOS cooperative carrier queue depth
2. Queue a direct value task on the current carrier
3. Verify value work is pending until the carrier runs
   - Expected: handle.is_done() is false
   - Expected: cooperative_green_ready_count() equals `before + 1`
4. Run one cooperative carrier turn
   - Expected: cooperative_green_run_one() is true
5. Verify the direct value result is returned
   - Expected: handle.join() equals `21`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Record the current SimpleOS cooperative carrier queue depth")
val before = cooperative_green_ready_count()
step("Queue a direct value task on the current carrier")
val handle = cooperative_green_spawn_value(21)

step("Verify value work is pending until the carrier runs")
expect(handle.is_done()).to_equal(false)
expect(cooperative_green_ready_count()).to_equal(before + 1)
step("Run one cooperative carrier turn")
expect(cooperative_green_run_one()).to_equal(true)
step("Verify the direct value result is returned")
expect(handle.join()).to_equal(21)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
