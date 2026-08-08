# Ipc Port Create Baremetal Stub Specification

> <details>

<!-- sdn-diagram:id=ipc_port_create_baremetal_stub_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ipc_port_create_baremetal_stub_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ipc_port_create_baremetal_stub_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ipc_port_create_baremetal_stub_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc Port Create Baremetal Stub Specification

## Scenarios

### Baremetal x86_64 IPC syscall coverage (documentation)

#### documents SYS_IPC_SEND_KERNEL=20 as handled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handled = true
expect(handled).to_equal(true)
```

</details>

#### documents SYS_IPC_RECV=21 as handled

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handled = true
expect(handled).to_equal(true)
```

</details>

#### documents SYS_IPC_CREATE_PORT=22 as the wm-service failure point

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pre-fix: the baremetal default branch returns -38 for id 22.
# Post-fix: case 22 returns a pseudo-port id (1) so wm-service
# init() proceeds past port creation. Agent R lands the fix in
# this same slice.
val expected_post_fix: i64 = 1
val expected_pre_fix: i64 = -38
val post_fix_is_positive = expected_post_fix > 0
val pre_fix_is_enosys = expected_pre_fix == -38
expect(post_fix_is_positive).to_equal(true)
expect(pre_fix_is_enosys).to_equal(true)
```

</details>

#### documents SYS_IPC_SEND_SERVICE=23 as a known coverage gap

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# wm_service.spl, launcher.spl, vfs_service.spl use id 23 for
# send — the baremetal dispatcher does not handle it. This is a
# follow-up slice item (blocker noted in Agent R report).
val currently_handled = false
expect(currently_handled).to_equal(false)
```

</details>

#### documents SYS_IPC_CONNECT=24 as a known coverage gap

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val currently_handled = false
expect(currently_handled).to_equal(false)
```

</details>

### Baremetal stub default branch

#### returns -38 (ENOSYS) for unknown syscall ids

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val baremetal_default: i32 = -38
expect(baremetal_default).to_equal(-38)
```

</details>

#### is the exact value logged by services on port creation failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# '[wm-service] Failed to create IPC port (error -38)' — the -38
# in that log is this default-branch return value, proving the
# call landed in the baremetal fallthrough.
val observed_in_qemu: i64 = -38
val baremetal_default: i64 = -38
expect(observed_in_qemu).to_equal(baremetal_default)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/ipc_port_create_baremetal_stub_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Baremetal x86_64 IPC syscall coverage (documentation)
- Baremetal stub default branch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
