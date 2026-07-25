# Wine Simpleos Exec Env Gate Specification

> <details>

<!-- sdn-diagram:id=wine_simpleos_exec_env_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_simpleos_exec_env_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_simpleos_exec_env_gate_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_simpleos_exec_env_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Simpleos Exec Env Gate Specification

## Scenarios

### Wine SimpleOS executable environment gate

#### lists VM, full-OS, and container evidence required before Wine readiness claims

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val required = wine_simpleos_exec_env_required_evidence()
expect(required.len()).to_equal(21)
expect(required[0]).to_equal("simpleos-qemu-vm")
expect(required[1]).to_equal("simpleos-full-os-boot")
expect(required[2]).to_equal("simpleos-kernel-syscall-abi")
expect(required[3]).to_equal("simpleos-kernel-scheduler")
expect(required[4]).to_equal("simpleos-kernel-vfs-service")
expect(required[10]).to_equal("simpleos-container-namespace")
expect(required[11]).to_equal("simpleos-container-pid-namespace")
expect(required[17]).to_equal("simpleos-container-rootfs-nvfs")
expect(required[18]).to_equal("simpleos-mdsoc-capsule")
expect(required[19]).to_equal("simpleos-mdsoc-public-port")
expect(required[20]).to_equal("simpleos-mdsoc-resident-state-owner")
```

</details>

#### reports the first missing executable-environment prerequisite

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val state = wine_simpleos_exec_env_gate("simpleos-qemu-vm simpleos-full-os-boot simpleos-user-process")
expect(state).to_equal("missing-simpleos-kernel-syscall-abi")
```

</details>

#### accepts the fixture evidence used by the composed Wine precondition manifest

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(wine_simpleos_exec_env_gate(wine_simpleos_exec_env_fixture_evidence())).to_equal("ready")
```

</details>

#### derives executable-environment evidence from QEMU desktop serial markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val evidence = wine_simpleos_exec_env_evidence_from_serial_log(wine_simpleos_exec_env_fixture_serial_log())
expect(evidence).to_contain("simpleos-qemu-vm")
expect(evidence).to_contain("simpleos-full-os-boot")
expect(evidence).to_contain("simpleos-kernel-syscall-abi")
expect(evidence).to_contain("simpleos-kernel-scheduler")
expect(evidence).to_contain("simpleos-kernel-vfs-service")
expect(evidence).to_contain("simpleos-user-process")
expect(evidence).to_contain("simpleos-vmspace")
expect(evidence).to_contain("simpleos-container-namespace")
expect(evidence).to_contain("simpleos-container-pid-namespace")
expect(evidence).to_contain("simpleos-container-fs-namespace")
expect(evidence).to_contain("simpleos-container-ipc-namespace")
expect(evidence).to_contain("simpleos-container-net-namespace")
expect(evidence).to_contain("simpleos-container-capability-boundary")
expect(evidence).to_contain("simpleos-container-rootfs")
expect(evidence).to_contain("simpleos-container-rootfs-nvfs")
expect(evidence).to_contain("simpleos-mdsoc-capsule")
expect(evidence).to_contain("simpleos-mdsoc-public-port")
expect(evidence).to_contain("simpleos-mdsoc-resident-state-owner")
expect(wine_simpleos_exec_env_gate_from_serial_log(wine_simpleos_exec_env_fixture_serial_log())).to_equal("ready")
```

</details>

#### keeps QEMU desktop evidence blocked until container namespace facets appear

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial_log = "QEMU x86_64 desktop lane\n" +
    "[phase-3-mount] fat32 ok\n" +
    "[kernel] syscall-abi:ok arch=x86_64\n" +
    "[kernel] scheduler:ok runqueue=user\n" +
    "[kernel] vfs-service:ok root=/\n" +
    "[vfs] mounted fat32 device=nvme0 volume=simpleos\n" +
    "[fs-exec] spawn:image path=/sys/apps/wine_hello entry=0 segments=1 stub_bytes=128\n" +
    "[desktop-e2e] process-backed:ok app=wine_hello pid=42\n" +
    "[desktop-e2e] wm:ok pid=42 wid=1001\n" +
    "[desktop-e2e] network-smoke:bounded ok packets=1\n" +
    "[desktop-e2e] container-namespace:ok\n" +
    "[desktop-e2e] container-rootfs:ok rootfs=/containers/wine rootfs_backend=nvfs\n" +
    "TEST PASSED"
expect(wine_simpleos_exec_env_gate_from_serial_log(serial_log)).to_equal("missing-simpleos-container-pid-namespace")
```

</details>

#### keeps full-OS boot evidence blocked until kernel OS services appear

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial_log = "QEMU x86_64 desktop lane\n" +
    "[phase-3-mount] fat32 ok\n" +
    "[vfs] mounted fat32 device=nvme0 volume=simpleos\n" +
    "[fs-exec] spawn:image path=/sys/apps/wine_hello entry=0 segments=1 stub_bytes=128\n" +
    "[desktop-e2e] process-backed:ok app=wine_hello pid=42\n" +
    "[desktop-e2e] wm:ok pid=42 wid=1001\n" +
    "[desktop-e2e] network-smoke:bounded ok packets=1\n" +
    "[desktop-e2e] container-namespace:ok pid fs ipc net capability\n" +
    "[desktop-e2e] container-rootfs:ok rootfs=/containers/wine rootfs_backend=nvfs\n" +
    "[desktop-e2e] mdsoc-capsule:ok owner=process-container-wm\n" +
    "[desktop-e2e] mdsoc-public-port:ok facade=exec-env\n" +
    "[desktop-e2e] mdsoc-resident-state-owner:ok ecs=wm,process,container\n" +
    "TEST PASSED"
expect(wine_simpleos_exec_env_gate_from_serial_log(serial_log)).to_equal("missing-simpleos-kernel-syscall-abi")
```

</details>

#### keeps QEMU desktop evidence blocked until container rootfs backend is nvfs

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial_log = "QEMU x86_64 desktop lane\n" +
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
    "[desktop-e2e] container-rootfs:ok rootfs=/containers/wine rootfs_backend=tmpfs\n" +
    "TEST PASSED"
expect(wine_simpleos_exec_env_gate_from_serial_log(serial_log)).to_equal("missing-simpleos-container-rootfs-nvfs")
```

</details>

#### keeps QEMU desktop evidence blocked until MDSOC resident ownership is proven

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val serial_log = "QEMU x86_64 desktop lane\n" +
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
expect(wine_simpleos_exec_env_gate_from_serial_log(serial_log)).to_equal("missing-simpleos-mdsoc-capsule")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/wine_simpleos_exec_env_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine SimpleOS executable environment gate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
