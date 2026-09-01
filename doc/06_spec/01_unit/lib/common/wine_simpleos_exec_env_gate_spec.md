# Wine Simpleos Exec Env Gate Specification

> Tests covering Wine SimpleOS executable environment gate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Simpleos Exec Env Gate Specification

## Scenarios

### Wine SimpleOS executable environment gate

#### lists VM, full-OS, and container evidence required before Wine readiness claims

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lists VM, full-OS, and container evidence required before Wine readiness claims
   - Expected: required.len() equals `21`
   - Expected: required[0] equals `simpleos-qemu-vm`
   - Expected: required[1] equals `simpleos-full-os-boot`
   - Expected: required[2] equals `simpleos-kernel-syscall-abi`
   - Expected: required[3] equals `simpleos-kernel-scheduler`
   - Expected: required[4] equals `simpleos-kernel-vfs-service`
   - Expected: required[10] equals `simpleos-container-namespace`
   - Expected: required[11] equals `simpleos-container-pid-namespace`
   - Expected: required[17] equals `simpleos-container-rootfs-nvfs`
   - Expected: required[18] equals `simpleos-mdsoc-capsule`
   - Expected: required[19] equals `simpleos-mdsoc-public-port`
   - Expected: required[20] equals `simpleos-mdsoc-resident-state-owner`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lists VM, full-OS, and container evidence required before Wine readiness claims")
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

- reports the first missing executable-environment prerequisite
   - Expected: state equals `missing-simpleos-kernel-syscall-abi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports the first missing executable-environment prerequisite")
val state = wine_simpleos_exec_env_gate("simpleos-qemu-vm simpleos-full-os-boot simpleos-user-process")
expect(state).to_equal("missing-simpleos-kernel-syscall-abi")
```

</details>

#### accepts the fixture evidence used by the composed Wine precondition manifest

- accepts the fixture evidence used by the composed Wine precondition manifest
   - Expected: wine_simpleos_exec_env_gate(wine_simpleos_exec_env_fixture_evidence()) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts the fixture evidence used by the composed Wine precondition manifest")
expect(wine_simpleos_exec_env_gate(wine_simpleos_exec_env_fixture_evidence())).to_equal("ready")
```

</details>

#### derives executable-environment evidence from QEMU desktop serial markers

- derives executable-environment evidence from QEMU desktop serial markers
   - Expected: wine_simpleos_exec_env_gate_from_serial_log(wine_simpleos_exec_env_fixture_serial_log()) equals `ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("derives executable-environment evidence from QEMU desktop serial markers")
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

- keeps QEMU desktop evidence blocked until container namespace facets appear
   - Expected: wine_simpleos_exec_env_gate_from_serial_log(serial_log) equals `missing-simpleos-container-pid-namespace`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps QEMU desktop evidence blocked until container namespace facets appear")
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

- keeps full-OS boot evidence blocked until kernel OS services appear
   - Expected: wine_simpleos_exec_env_gate_from_serial_log(serial_log) equals `missing-simpleos-kernel-syscall-abi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps full-OS boot evidence blocked until kernel OS services appear")
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

- keeps QEMU desktop evidence blocked until container rootfs backend is nvfs
   - Expected: wine_simpleos_exec_env_gate_from_serial_log(serial_log) equals `missing-simpleos-container-rootfs-nvfs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps QEMU desktop evidence blocked until container rootfs backend is nvfs")
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

- keeps QEMU desktop evidence blocked until MDSOC resident ownership is proven
   - Expected: wine_simpleos_exec_env_gate_from_serial_log(serial_log) equals `missing-simpleos-mdsoc-capsule`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps QEMU desktop evidence blocked until MDSOC resident ownership is proven")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine SimpleOS executable environment gate.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4af66783a111e6ec3b50d29be1f6ebc5a45c53e5f5b2ae67ecd2dbb1c075dcbc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4af66783a111e6ec3b50d29be1f6ebc5a45c53e5f5b2ae67ecd2dbb1c075dcbc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4af66783a111e6ec3b50d29be1f6ebc5a45c53e5f5b2ae67ecd2dbb1c075dcbc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/wine_simpleos_exec_env_gate_spec.spl
mirror: doc/06_spec/01_unit/lib/common/wine_simpleos_exec_env_gate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/wine_simpleos_exec_env_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/wine_simpleos_exec_env_gate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/wine_simpleos_exec_env_gate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/wine_simpleos_exec_env_gate_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the first missing executable-environment prerequisite' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_simpleos_exec_env_gate_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives executable-environment evidence from QEMU desktop serial markers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/wine_simpleos_exec_env_gate_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps QEMU desktop evidence blocked until container namespace facets appear' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
