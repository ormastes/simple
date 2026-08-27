# Test Daemon Multi Session System Specification

> <details>

<!-- sdn-diagram:id=test_daemon_multi_session_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_multi_session_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_multi_session_system_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_multi_session_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Daemon Multi Session System Specification

## Scenarios

### Multi-session coordination portable smoke

#### keeps session kinds distinct

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qemu_kind = "qemu"
val container_kind = "container"
expect(qemu_kind).to_equal("qemu")
expect(container_kind).to_equal("container")
```

</details>

#### records reuse policies

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shared_read_only = "shared_read_only"
val fresh_per_test = "fresh_per_test"
expect(shared_read_only).to_contain("shared")
expect(fresh_per_test).to_contain("fresh")
```

</details>

#### records multi-architecture keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val targets = ["arm64", "riscv64", "x86_64"]
expect(targets.len()).to_equal(3)
expect(targets[1]).to_equal("riscv64")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/test_daemon/test_daemon_multi_session_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Multi-session coordination portable smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
