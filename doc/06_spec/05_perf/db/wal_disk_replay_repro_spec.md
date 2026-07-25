# Wal Disk Replay Repro Specification

> <details>

<!-- sdn-diagram:id=wal_disk_replay_repro_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wal_disk_replay_repro_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wal_disk_replay_repro_spec -> std
wal_disk_replay_repro_spec -> nogc_sync_mut
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wal_disk_replay_repro_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wal Disk Replay Repro Specification

## Scenarios

### wal disk replay isolation

#### reconstructs exact field data

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(replay_field()).to_equal("42|420|bench.txt")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/db/wal_disk_replay_repro_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wal disk replay isolation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
