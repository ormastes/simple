# Replay Offmode Overhead Specification

> <details>

<!-- sdn-diagram:id=replay_offmode_overhead_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replay_offmode_overhead_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replay_offmode_overhead_spec -> std
replay_offmode_overhead_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replay_offmode_overhead_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Replay Offmode Overhead Specification

## Scenarios

### SReplay Track 2.10 — off-mode overhead

#### replay_hook_schedule 1000 calls in Off mode completes <100ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms = _bench_schedule()
expect(ms).to_be_less_than(100)
```

</details>

#### replay_hook_syscall_enter 1000 calls in Off mode completes <100ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms = _bench_syscall_enter()
expect(ms).to_be_less_than(100)
```

</details>

#### replay_hook_irq 1000 calls in Off mode completes <100ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms = _bench_irq()
expect(ms).to_be_less_than(100)
```

</details>

#### replay_hook_timer_read 1000 calls in Off mode returns quickly <100ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms = _bench_timer_read()
expect(ms).to_be_less_than(100)
```

</details>

#### mode is Off after explicit init

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ok = _mode_off_after_init()
expect(ok).to_equal(true)
```

</details>

#### Off -> Record -> Off leaves no residual overhead (<100ms)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ms = _bench_off_record_off()
expect(ms).to_be_less_than(100)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/replay_offmode_overhead_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SReplay Track 2.10 — off-mode overhead

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
