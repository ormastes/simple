# Channel Native Overflow Specification

> 1. rt channel send

<!-- sdn-diagram:id=channel_native_overflow_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=channel_native_overflow_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

channel_native_overflow_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=channel_native_overflow_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Channel Native Overflow Specification

## Scenarios

### Native channel overflow

#### preserves messages beyond the old fixed native ring size

1. rt channel send

2. rt exit

3. rt channel close


<details>
<summary>Executable SPipe</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val channel_id = rt_channel_new()
var sent = 1
while sent <= 1100:
    rt_channel_send(channel_id, sent)
    sent = sent + 1

var received = 1
while received <= 1100:
    val value = rt_channel_try_recv(channel_id)
    if value != received:
        rt_exit(11)
    received = received + 1

rt_channel_close(channel_id)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/channel_native_overflow_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Native channel overflow

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
