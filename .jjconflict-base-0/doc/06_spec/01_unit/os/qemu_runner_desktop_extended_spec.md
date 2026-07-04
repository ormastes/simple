# Qemu Runner Desktop Extended Specification

> <details>

<!-- sdn-diagram:id=qemu_runner_desktop_extended_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qemu_runner_desktop_extended_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qemu_runner_desktop_extended_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qemu_runner_desktop_extended_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qemu Runner Desktop Extended Specification

## Scenarios

### Qemu runner desktop UEFI tool app validator

#### requires clang in the x64 desktop live acceptance marker set

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val markers = desktop_uefi_required_marker_fragments()
expect(markers).to_contain("[desktop-e2e] process-backed:ok app=clang pid=")
expect(markers).to_contain("[desktop-e2e] native-toolchain-launch:ok app=clang lane=x86_64-uefi-hardware mode=native-filesystem-app status=standalone-required tool=/sys/apps/clang manifest=/SYS/CLANGMAN.TXT")
expect(markers).to_contain("[desktop-e2e] native-capability:ok app=clang capability=local-c-source-inspection proof=/usr/share/simpleos/toolchain/clang/hello.c")
expect(markers).to_contain("[desktop-e2e] native-capability:ok app=clang capability=driver-flag-inspection proof=/usr/share/simpleos/toolchain/clang/flags.rsp")
expect(markers).to_contain("[desktop-e2e] native-capability:ok app=clang capability=compile-pipeline-step proof=/usr/share/simpleos/toolchain/clang/pipeline.step")
```

</details>

#### requires validated container namespace and rootfs markers in x64 desktop acceptance

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val container_markers = desktop_container_marker_fragments()
val uefi_markers = desktop_uefi_required_marker_fragments()
expect(container_markers).to_equal(["[desktop-e2e] container-namespace:ok", "[desktop-e2e] container-rootfs:ok"])
expect(uefi_markers).to_contain("[desktop-e2e] container-namespace:ok")
expect(uefi_markers).to_contain("[desktop-e2e] container-rootfs:ok")
```

</details>

#### requires Wine hello to be VFS-backed and spawned in x64 desktop acceptance

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val markers = desktop_uefi_required_marker_fragments()
expect(markers).to_contain("[desktop-e2e] vfs-app-read:ok source=generic-vfs path=/sys/apps/wine_hello bytes=")
expect(markers).to_contain("[fs-exec] spawn:image path=/sys/apps/wine_hello")
expect(markers).to_contain("[desktop-e2e] process-backed:ok app=wine_hello pid=")
```

</details>

#### defines the extra Wine executable-environment markers needed before readiness claims

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val markers = desktop_wine_exec_env_required_marker_fragments()
expect(markers).to_contain("[fs-exec] spawn:image path=/sys/apps/wine_hello")
expect(markers).to_contain("[desktop-e2e] process-backed:ok app=wine_hello pid=")
expect(markers).to_contain("[desktop-e2e] container-namespace:ok")
expect(markers).to_contain("[desktop-e2e] container-rootfs:ok")

val serial = "QEMU x86_64 desktop lane\n" +
    "[phase-3-mount] fat32 ok\n" +
    "[kernel] syscall-abi:ok arch=x86_64\n" +
    "[kernel] scheduler:ok runqueue=user\n" +
    "[kernel] vfs-service:ok root=/\n" +
    "[vfs] mounted fat32 device=nvme0 volume=simpleos\n" +
    "[fs-exec] spawn:image path=/sys/apps/wine_hello entry=0 segments=1 stub_bytes=128 argv_count=1 env_count=0\n" +
    "[desktop-e2e] process-backed:ok app=wine_hello pid=42\n" +
    "[desktop-e2e] wm:ok pid=42 wid=1001\n" +
    "[desktop-e2e] network-smoke:bounded ok packets=1\n" +
    "[desktop-e2e] container-namespace:ok pid fs ipc net capability\n" +
    "[desktop-e2e] container-rootfs:ok rootfs=/containers/wine rootfs_backend=nvfs\n" +
    "[desktop-e2e] mdsoc-capsule:ok owner=process-container-wm\n" +
    "[desktop-e2e] mdsoc-public-port:ok facade=exec-env\n" +
    "[desktop-e2e] mdsoc-resident-state-owner:ok ecs=wm,process,container\n" +
    "TEST PASSED"
expect(desktop_wine_exec_env_marker_contract_accepts(serial)).to_equal(true)
expect(desktop_wine_exec_env_marker_contract_accepts(serial.replace("[desktop-e2e] container-rootfs:ok", "[desktop-e2e] container-rootfs:missing"))).to_equal(false)
```

</details>

#### captures the x64 desktop disk probe terminal serial pass marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-x64-desktop-disk-probe"
val serial = root + "/serial.log"
expect(rt_dir_create_all(root)).to_equal(true)
val (stdout, _stderr, exit_code) = run_x64_desktop_disk_probe(
    ["/bin/sh", "-c", "'printf \"boot\\\\nTEST PASSED\\\\n\"'"],
    serial,
    1500)
expect(exit_code).to_equal(0)
expect(stdout).to_contain("TEST PASSED")
```

</details>

#### requires clang in the riscv64 hosted acceptance marker set

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val markers = riscv64_hosted_required_marker_fragments()
expect(markers).to_contain("[desktop-e2e] process-backed:ok app=clang pid=")
expect(markers).to_contain("[desktop-e2e] native-toolchain-launch:ok app=clang lane=riscv64-hosted mode=native-filesystem-app status=standalone-required tool=/sys/apps/clang manifest=/SYS/CLANGMAN.TXT")
expect(markers).to_contain("HOSTED_FS_TOOLCHAIN_READY arch=riscv64 apps=simple_compiler,simple_loader,llvm,clang,rust")
val lane = simpleos_platform_qemu_lane("riscv64", "riscv64-hosted")
if val resolved_lane = lane:
    expect(markers).to_equal(resolved_lane.required_serial_markers)
else:
    fail("missing riscv64 hosted lane")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/qemu_runner_desktop_extended_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Qemu runner desktop UEFI tool app validator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
