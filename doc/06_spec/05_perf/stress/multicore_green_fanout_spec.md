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

<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val iterations = 512
val expected = fanout_expected(8, iterations)

val h0 = thread_spawn_with_args(0, iterations, \seed, iters: fanout_work(seed, iters))
val h1 = thread_spawn_with_args(1, iterations, \seed, iters: fanout_work(seed, iters))
val h2 = thread_spawn_with_args(2, iterations, \seed, iters: fanout_work(seed, iters))
val h3 = thread_spawn_with_args(3, iterations, \seed, iters: fanout_work(seed, iters))
val h4 = thread_spawn_with_args(4, iterations, \seed, iters: fanout_work(seed, iters))
val h5 = thread_spawn_with_args(5, iterations, \seed, iters: fanout_work(seed, iters))
val h6 = thread_spawn_with_args(6, iterations, \seed, iters: fanout_work(seed, iters))
val h7 = thread_spawn_with_args(7, iterations, \seed, iters: fanout_work(seed, iters))

val got = h0.join() + h1.join() + h2.join() + h3.join() + h4.join() + h5.join() + h6.join() + h7.join()
expect(got).to_equal(expected)
```

</details>


</details>

<details>
<summary>Advanced: matches cooperative-green fanout checksum on the current carrier</summary>

#### matches cooperative-green fanout checksum on the current carrier _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val iterations = 512
val expected = fanout_expected(8, iterations)

val h0 = cooperative_green_spawn_value(fanout_work(0, iterations))
val h1 = cooperative_green_spawn_value(fanout_work(1, iterations))
val h2 = cooperative_green_spawn_value(fanout_work(2, iterations))
val h3 = cooperative_green_spawn_value(fanout_work(3, iterations))
val h4 = cooperative_green_spawn_value(fanout_work(4, iterations))
val h5 = cooperative_green_spawn_value(fanout_work(5, iterations))
val h6 = cooperative_green_spawn_value(fanout_work(6, iterations))
val h7 = cooperative_green_spawn_value(fanout_work(7, iterations))

val ran = cooperative_green_run_all()
val got = h0.join() + h1.join() + h2.join() + h3.join() + h4.join() + h5.join() + h6.join() + h7.join()

expect(ran >= 8).to_equal(true)
expect(got).to_equal(expected)
```

</details>


</details>

<details>
<summary>Advanced: matches multicore-green fanout checksum and reports M:N evidence</summary>

#### matches multicore-green fanout checksum and reports M:N evidence _(slow)_

<details>
<summary>Executable SPipe</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val iterations = 512
val expected = fanout_expected(8, iterations)

val h0 = multicore_green_spawn(\: fanout_work(0, iterations))
val h1 = multicore_green_spawn(\: fanout_work(1, iterations))
val h2 = multicore_green_spawn(\: fanout_work(2, iterations))
val h3 = multicore_green_spawn(\: fanout_work(3, iterations))
val h4 = multicore_green_spawn(\: fanout_work(4, iterations))
val h5 = multicore_green_spawn(\: fanout_work(5, iterations))
val h6 = multicore_green_spawn(\: fanout_work(6, iterations))
val h7 = multicore_green_spawn(\: fanout_work(7, iterations))

var pool_used = 0
var inline_fallback = 0
if h0.used_runtime_pool(): pool_used = pool_used + 1
if h1.used_runtime_pool(): pool_used = pool_used + 1
if h2.used_runtime_pool(): pool_used = pool_used + 1
if h3.used_runtime_pool(): pool_used = pool_used + 1
if h4.used_runtime_pool(): pool_used = pool_used + 1
if h5.used_runtime_pool(): pool_used = pool_used + 1
if h6.used_runtime_pool(): pool_used = pool_used + 1
if h7.used_runtime_pool(): pool_used = pool_used + 1
if h0.ran_inline_fallback(): inline_fallback = inline_fallback + 1
if h1.ran_inline_fallback(): inline_fallback = inline_fallback + 1
if h2.ran_inline_fallback(): inline_fallback = inline_fallback + 1
if h3.ran_inline_fallback(): inline_fallback = inline_fallback + 1
if h4.ran_inline_fallback(): inline_fallback = inline_fallback + 1
if h5.ran_inline_fallback(): inline_fallback = inline_fallback + 1
if h6.ran_inline_fallback(): inline_fallback = inline_fallback + 1
if h7.ran_inline_fallback(): inline_fallback = inline_fallback + 1

val got = h0.join() + h1.join() + h2.join() + h3.join() + h4.join() + h5.join() + h6.join() + h7.join()
val has_mn_evidence = pool_used == 8

expect(got).to_equal(expected)
expect(pool_used + inline_fallback).to_equal(8)
expect(has_mn_evidence or inline_fallback == 8).to_equal(true)
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
