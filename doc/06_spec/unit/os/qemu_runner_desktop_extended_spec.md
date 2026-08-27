# Qemu Runner Desktop Extended Specification

> Tests covering Qemu runner desktop UEFI tool app validator.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Qemu Runner Desktop Extended Specification

## Scenarios

### Qemu runner desktop UEFI tool app validator

#### requires clang in the x64 desktop live acceptance marker set

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires clang in the x64 desktop live acceptance marker set


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires clang in the x64 desktop live acceptance marker set")
val markers = desktop_uefi_required_marker_fragments()
expect(markers).to_contain("[desktop-e2e] process-backed:ok app=clang pid=")
expect(markers).to_contain("[desktop-e2e] native-toolchain-launch:ok app=clang lane=x86_64-uefi-hardware mode=native-filesystem-app status=standalone-required tool=/sys/apps/clang manifest=/SYS/CLANGMAN.TXT")
expect(markers).to_contain("[desktop-e2e] native-capability:ok app=clang capability=local-c-source-inspection proof=/usr/share/simpleos/toolchain/clang/hello.c")
expect(markers).to_contain("[desktop-e2e] native-capability:ok app=clang capability=driver-flag-inspection proof=/usr/share/simpleos/toolchain/clang/flags.rsp")
expect(markers).to_contain("[desktop-e2e] native-capability:ok app=clang capability=compile-pipeline-step proof=/usr/share/simpleos/toolchain/clang/pipeline.step")
```

</details>

#### requires validated container namespace and rootfs markers in x64 desktop acceptance

- requires validated container namespace and rootfs markers in x64 desktop acceptance
   - Expected: container_markers equals `["[desktop-e2e] container-namespace:ok", "[desktop-e2e] container-rootfs:ok"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires validated container namespace and rootfs markers in x64 desktop acceptance")
val container_markers = desktop_container_marker_fragments()
val uefi_markers = desktop_uefi_required_marker_fragments()
expect(container_markers).to_equal(["[desktop-e2e] container-namespace:ok", "[desktop-e2e] container-rootfs:ok"])
expect(uefi_markers).to_contain("[desktop-e2e] container-namespace:ok")
expect(uefi_markers).to_contain("[desktop-e2e] container-rootfs:ok")
```

</details>

#### requires Wine hello to be VFS-backed and spawned in x64 desktop acceptance

- requires Wine hello to be VFS-backed and spawned in x64 desktop acceptance


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires Wine hello to be VFS-backed and spawned in x64 desktop acceptance")
val markers = desktop_uefi_required_marker_fragments()
expect(markers).to_contain("[desktop-e2e] vfs-app-read:ok source=generic-vfs path=/sys/apps/wine_hello bytes=")
expect(markers).to_contain("[fs-exec] spawn:image path=/sys/apps/wine_hello")
expect(markers).to_contain("[desktop-e2e] process-backed:ok app=wine_hello pid=")
```

</details>

#### defines the extra Wine executable-environment markers needed before readiness claims

- defines the extra Wine executable-environment markers needed before readiness claims
   - Expected: desktop_wine_exec_env_marker_contract_accepts(serial) is true
   - Expected: desktop_wine_exec_env_marker_contract_accepts(serial.replace("[desktop-e2e] container-rootfs:ok", "[desktop-e2e] container-rootfs:missing")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines the extra Wine executable-environment markers needed before readiness claims")
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

- captures the x64 desktop disk probe terminal serial pass marker
   - Expected: rt_dir_create_all(root) is true
   - Expected: exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("captures the x64 desktop disk probe terminal serial pass marker")
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

- requires clang in the riscv64 hosted acceptance marker set
   - Expected: markers equals `resolved_lane.required_serial_markers`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires clang in the riscv64 hosted acceptance marker set")
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
| Source | `test/unit/os/qemu_runner_desktop_extended_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Qemu runner desktop UEFI tool app validator.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ec760e2fe736357a80105c05a9b7c757346377da8e5f3998857e155e5877005d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ec760e2fe736357a80105c05a9b7c757346377da8e5f3998857e155e5877005d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ec760e2fe736357a80105c05a9b7c757346377da8e5f3998857e155e5877005d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/os/qemu_runner_desktop_extended_spec.spl
mirror: doc/06_spec/unit/os/qemu_runner_desktop_extended_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/qemu_runner_desktop_extended_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/qemu_runner_desktop_extended_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/qemu_runner_desktop_extended_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/qemu_runner_desktop_extended_spec.spl:203:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires clang in the x64 desktop live acceptance marker set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/qemu_runner_desktop_extended_spec.spl:213:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires validated container namespace and rootfs markers in x64 desktop acceptance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/qemu_runner_desktop_extended_spec.spl:222:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires Wine hello to be VFS-backed and spawned in x64 desktop acceptance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
