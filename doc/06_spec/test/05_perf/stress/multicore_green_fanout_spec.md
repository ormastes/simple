# Multicore Green Fanout Stress Specification

> This perf stress spec keeps the Simple concurrency rows comparable: OS threads, cooperative green, and multicore green all run the same deterministic fanout workload and must produce the same checksum. The multicore-green row separately reports whether every handle used the runtime pool, so inline fallback cannot be mistaken for Go-like M:N CPU-parallel evidence.

<!-- sdn-diagram:id=multicore_green_fanout_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=multicore_green_fanout_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

multicore_green_fanout_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=multicore_green_fanout_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Multicore Green Fanout Stress Specification

This perf stress spec keeps the Simple concurrency rows comparable: OS threads, cooperative green, and multicore green all run the same deterministic fanout workload and must produce the same checksum. The multicore-green row separately reports whether every handle used the runtime pool, so inline fallback cannot be mistaken for Go-like M:N CPU-parallel evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #green-perf-fanout |
| Category | Performance / Concurrency |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/multicore_green.md |
| Design | N/A |
| Research | doc/01_research/local/multicore_green.md |
| Source | `test/05_perf/stress/multicore_green_fanout_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This perf stress spec keeps the Simple concurrency rows comparable: OS threads,
cooperative green, and multicore green all run the same deterministic fanout
workload and must produce the same checksum. The multicore-green row separately
reports whether every handle used the runtime pool, so inline fallback cannot be
mistaken for Go-like M:N CPU-parallel evidence.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** doc/03_plan/sys_test/multicore_green.md

## Design

**Design:** N/A

## Research

**Research:** doc/01_research/local/multicore_green.md

## Scenarios

### multicore green fanout stress

<details>
<summary>Advanced: matches OS-thread fanout/fanin checksum</summary>

#### matches OS-thread fanout/fanin checksum _(slow)_

1. Spawn OS-thread fanout handles with a compact handle array
2. Join OS-thread handles and compare the deterministic checksum
   - Expected: got equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val iterations = 512
val worker_count = 8
val expected = fanout_expected(worker_count, iterations)

step("Spawn OS-thread fanout handles with a compact handle array")
val handles = spawn_os_thread_handles(worker_count, iterations)

step("Join OS-thread handles and compare the deterministic checksum")
val got = join_os_thread_handles(handles)
expect(got).to_equal(expected)
```

</details>


</details>

<details>
<summary>Advanced: matches cooperative-green fanout checksum on the current carrier</summary>

#### matches cooperative-green fanout checksum on the current carrier _(slow)_

1. Queue cooperative-green value handles on the current carrier
2. Drain the cooperative queue and join every handle
   - Expected: ran >= worker_count is true
   - Expected: got equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val iterations = 512
val worker_count = 8
val expected = fanout_expected(worker_count, iterations)

step("Queue cooperative-green value handles on the current carrier")
val handles = spawn_cooperative_green_handles(worker_count, iterations)

step("Drain the cooperative queue and join every handle")
val ran = cooperative_green_run_all()
val got = join_cooperative_green_handles(handles)

expect(ran >= worker_count).to_equal(true)
expect(got).to_equal(expected)
```

</details>


</details>

<details>
<summary>Advanced: matches multicore-green fanout checksum and reports M:N evidence</summary>

#### matches multicore-green fanout checksum and reports M:N evidence _(slow)_

1. Spawn multicore-green handles through the runtime-pool facade
2. Join multicore-green handles and count runtime-pool evidence
   - Expected: evidence.got equals `expected`
   - Expected: evidence.pool_used + evidence.inline_fallback equals `worker_count`
   - Expected: has_mn_evidence or evidence.inline_fallback == worker_count is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val iterations = 512
val worker_count = 8
val expected = fanout_expected(worker_count, iterations)

step("Spawn multicore-green handles through the runtime-pool facade")
val handles = spawn_multicore_green_handles(worker_count, iterations)

step("Join multicore-green handles and count runtime-pool evidence")
val evidence = join_multicore_green_handles(handles)
val has_mn_evidence = evidence.pool_used == worker_count

expect(evidence.got).to_equal(expected)
expect(evidence.pool_used + evidence.inline_fallback).to_equal(worker_count)
expect(has_mn_evidence or evidence.inline_fallback == worker_count).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/multicore_green.md](doc/03_plan/sys_test/multicore_green.md)
- **Research:** [doc/01_research/local/multicore_green.md](doc/01_research/local/multicore_green.md)


</details>
