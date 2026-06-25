# Simpleos Exec Env Mdsoc Specification

> <details>

<!-- sdn-diagram:id=simpleos_exec_env_mdsoc_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_exec_env_mdsoc_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_exec_env_mdsoc_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_exec_env_mdsoc_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Exec Env Mdsoc Specification

## Scenarios

### SimpleOS executable environment MDSOC gate

#### requires MDSOC capsule, public port, and resident owner evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val missing_mdsoc = "QEMU x86_64 desktop lane\n" +
    "[phase-3-mount] fat32 ok\n" +
    "[kernel] syscall-abi:ok arch=x86_64\n" +
    "[kernel] scheduler:ok runqueue=user\n" +
    "[kernel] vfs-service:ok root=/\n" +
    "[vfs] mounted fat32 device=nvme0 volume=simpleos\n" +
    "[fs-exec] spawn:image path=/sys/apps/wine_hello entry=0 segments=1 stub_bytes=128\n" +
    "[desktop-e2e] process-backed:ok app=wine_hello pid=42\n" +
    "[desktop-e2e] wm:ok pid=42 wid=1001\n" +
    "[desktop-e2e] network-smoke:bounded ok packets=1\n" +
    "[desktop-e2e] container-namespace:ok pid fs ipc net capability\n" +
    "[desktop-e2e] container-rootfs:ok rootfs=/containers/wine rootfs_backend=nvfs\n" +
    "TEST PASSED"
expect(wine_simpleos_exec_env_gate_from_serial_log(missing_mdsoc)).to_equal("missing-simpleos-mdsoc-capsule")

val ready = missing_mdsoc +
    "[desktop-e2e] mdsoc-capsule:ok owner=process-container-wm\n" +
    "[desktop-e2e] mdsoc-public-port:ok facade=exec-env\n" +
    "[desktop-e2e] mdsoc-resident-state-owner:ok ecs=wm,process,container\n"
expect(wine_simpleos_exec_env_gate_from_serial_log(ready)).to_equal("ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos/feature/simpleos_exec_env_mdsoc_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS executable environment MDSOC gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
