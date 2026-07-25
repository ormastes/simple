# Ipc L4 Logic Perf Specification

> <details>

<!-- sdn-diagram:id=ipc_l4_logic_perf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ipc_l4_logic_perf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ipc_l4_logic_perf_spec -> std
ipc_l4_logic_perf_spec -> test
ipc_l4_logic_perf_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ipc_l4_logic_perf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc L4 Logic Perf Specification

## Scenarios

### L4 IPC logic performance contract

<details>
<summary>Advanced: keeps inline register IPC materially faster than queued manager send/recv</summary>

#### keeps inline register IPC materially faster than queued manager send/recv _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val iters: i64 = 20000
val current = _bench_current_ipc_queue_ns(iters)
val inline32 = _bench_l4_inline32_ns(iters)
val inline64 = _bench_l4_inline64_ns(iters)

print "ipc-perf current_ns={current[0]} inline32_ns={inline32[0]} inline64_ns={inline64[0]} iters={iters}"
expect(current[1]).to_be_greater_than(0)
expect(inline32[1]).to_be_greater_than(0)
expect(inline64[1]).to_be_greater_than(0)
expect(inline32[0] * 2).to_be_less_than(current[0])
expect(inline64[0] * 2).to_be_less_than(current[0])
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/ipc_l4_logic_perf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- L4 IPC logic performance contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
