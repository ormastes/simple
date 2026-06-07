# Wine Host Gate Specification

> <details>

<!-- sdn-diagram:id=wine_host_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_host_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_host_gate_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_host_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Host Gate Specification

## Scenarios

### Wine host substrate gate

### overall host features

#### lists POSIX, thread, loader, and service features

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val required = wine_host_required_features()
expect(required.len()).to_be_greater_than(20)
expect(required[0]).to_equal("fd-table")
```

</details>

#### reports the first missing host feature

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_host_gate("fd-table stdio pipes sockets poll-wait timers errno cwd-env-argv spawn fs-paths")
expect(state).to_equal("missing-fs-attrs")
```

</details>

### specific service gates

#### requires real pthread, TLS, synchronization, and fault attribution

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_thread_gate("pthread tls mutex condvar semaphore event")
expect(state).to_equal("missing-thread-fault")
```

</details>

#### requires POSIX-shaped fd, wait, timer, env, and spawn services

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_posix_gate("fd-table stdio pipes sockets poll-wait timers errno cwd-env-argv")
expect(state).to_equal("missing-spawn")
```

</details>

#### requires dynamic loading and structured loader behavior

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_dynamic_gate("dynload symbol-lookup relocation")
expect(state).to_equal("missing-loader-errors")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_host_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine host substrate gate
- overall host features
- specific service gates

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
