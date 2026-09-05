# Architecture, filesystem, and authenticated execution

> Defines fail-closed live acceptance for three architectures, FAT32/DBFS/NVFS, authenticated open-handle loading, and durability.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Architecture, filesystem, and authenticated execution

Defines fail-closed live acceptance for three architectures, FAT32/DBFS/NVFS, authenticated open-handle loading, and durability.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_arch_fs_exec_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Defines fail-closed live acceptance for three architectures, FAT32/DBFS/NVFS, authenticated open-handle loading, and durability.

This is an explicit BLOCKED traceability spec. Each checker validates a
structurally complete blocked candidate through the production capability-ledger
owner and reports its executable owner, exact expected receipt, and resume
command. A row cannot pass until that receipt is produced and admitted.

## Scenarios

### REQ-002: three-architecture system execution

#### should accept complete live evidence for three-architecture system execution

- should accept complete live evidence for three-architecture system execution
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for three-architecture system execution")
step_boot_target()
check_simpleos_capability_matrix("REQ-002", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for three-architecture system execution</summary>

#### should preserve the selected boundary for three-architecture system execution

- should preserve the selected boundary for three-architecture system execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for three-architecture system execution")
step_boot_target()
check_simpleos_capability_matrix("REQ-002", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for three-architecture system execution</summary>

#### should reject missing stale substituted or invalid evidence for three-architecture system execution

- should reject missing stale substituted or invalid evidence for three-architecture system execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for three-architecture system execution")
step_boot_target()
check_simpleos_capability_matrix("REQ-002", "rejection")
```

</details>


</details>

### REQ-003: shared filesystem contract

#### should accept complete live evidence for shared filesystem contract

- should accept complete live evidence for shared filesystem contract
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for shared filesystem contract")
step_mount_filesystem()
check_simpleos_filesystem_conformance("REQ-003", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for shared filesystem contract</summary>

#### should preserve the selected boundary for shared filesystem contract

- should preserve the selected boundary for shared filesystem contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for shared filesystem contract")
step_mount_filesystem()
check_simpleos_filesystem_conformance("REQ-003", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for shared filesystem contract</summary>

#### should reject missing stale substituted or invalid evidence for shared filesystem contract

- should reject missing stale substituted or invalid evidence for shared filesystem contract


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for shared filesystem contract")
step_mount_filesystem()
check_simpleos_filesystem_conformance("REQ-003", "rejection")
```

</details>


</details>

### REQ-004: FAT32 interoperability and recovery

#### should accept complete live evidence for FAT32 interoperability and recovery

- should accept complete live evidence for FAT32 interoperability and recovery
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for FAT32 interoperability and recovery")
step_mount_filesystem()
check_simpleos_filesystem_conformance("REQ-004", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for FAT32 interoperability and recovery</summary>

#### should preserve the selected boundary for FAT32 interoperability and recovery

- should preserve the selected boundary for FAT32 interoperability and recovery


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for FAT32 interoperability and recovery")
step_mount_filesystem()
check_simpleos_filesystem_conformance("REQ-004", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for FAT32 interoperability and recovery</summary>

#### should reject missing stale substituted or invalid evidence for FAT32 interoperability and recovery

- should reject missing stale substituted or invalid evidence for FAT32 interoperability and recovery


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for FAT32 interoperability and recovery")
step_mount_filesystem()
check_simpleos_filesystem_conformance("REQ-004", "rejection")
```

</details>


</details>

### REQ-005: DBFS durability and recovery

#### should accept complete live evidence for DBFS durability and recovery

- should accept complete live evidence for DBFS durability and recovery
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for DBFS durability and recovery")
step_mount_filesystem()
check_simpleos_filesystem_conformance("REQ-005", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for DBFS durability and recovery</summary>

#### should preserve the selected boundary for DBFS durability and recovery

- should preserve the selected boundary for DBFS durability and recovery


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for DBFS durability and recovery")
step_mount_filesystem()
check_simpleos_filesystem_conformance("REQ-005", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for DBFS durability and recovery</summary>

#### should reject missing stale substituted or invalid evidence for DBFS durability and recovery

- should reject missing stale substituted or invalid evidence for DBFS durability and recovery


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for DBFS durability and recovery")
step_mount_filesystem()
check_simpleos_filesystem_conformance("REQ-005", "rejection")
```

</details>


</details>

### REQ-006: NVFS durability and recovery

#### should accept complete live evidence for NVFS durability and recovery

- should accept complete live evidence for NVFS durability and recovery
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for NVFS durability and recovery")
step_mount_filesystem()
check_simpleos_filesystem_conformance("REQ-006", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for NVFS durability and recovery</summary>

#### should preserve the selected boundary for NVFS durability and recovery

- should preserve the selected boundary for NVFS durability and recovery


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for NVFS durability and recovery")
step_mount_filesystem()
check_simpleos_filesystem_conformance("REQ-006", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for NVFS durability and recovery</summary>

#### should reject missing stale substituted or invalid evidence for NVFS durability and recovery

- should reject missing stale substituted or invalid evidence for NVFS durability and recovery


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for NVFS durability and recovery")
step_mount_filesystem()
check_simpleos_filesystem_conformance("REQ-006", "rejection")
```

</details>


</details>

### REQ-007: authenticated executable loading

#### should accept complete live evidence for authenticated executable loading

- should accept complete live evidence for authenticated executable loading
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for authenticated executable loading")
step_launch_from_filesystem()
check_simpleos_filesystem_exec("REQ-007", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for authenticated executable loading</summary>

#### should preserve the selected boundary for authenticated executable loading

- should preserve the selected boundary for authenticated executable loading


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for authenticated executable loading")
step_launch_from_filesystem()
check_simpleos_filesystem_exec("REQ-007", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for authenticated executable loading</summary>

#### should reject missing stale substituted or invalid evidence for authenticated executable loading

- should reject missing stale substituted or invalid evidence for authenticated executable loading


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for authenticated executable loading")
step_launch_from_filesystem()
check_simpleos_filesystem_exec("REQ-007", "rejection")
```

</details>


</details>

### REQ-008: backend-neutral program execution

#### should accept complete live evidence for backend-neutral program execution

- should accept complete live evidence for backend-neutral program execution
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for backend-neutral program execution")
step_launch_from_filesystem()
check_simpleos_filesystem_exec("REQ-008", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for backend-neutral program execution</summary>

#### should preserve the selected boundary for backend-neutral program execution

- should preserve the selected boundary for backend-neutral program execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for backend-neutral program execution")
step_launch_from_filesystem()
check_simpleos_filesystem_exec("REQ-008", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for backend-neutral program execution</summary>

#### should reject missing stale substituted or invalid evidence for backend-neutral program execution

- should reject missing stale substituted or invalid evidence for backend-neutral program execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for backend-neutral program execution")
step_launch_from_filesystem()
check_simpleos_filesystem_exec("REQ-008", "rejection")
```

</details>


</details>

### NFR-006: authenticated execution safety

#### should accept complete live evidence for authenticated execution safety

- should accept complete live evidence for authenticated execution safety
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for authenticated execution safety")
step_launch_from_filesystem()
check_simpleos_filesystem_exec("NFR-006", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for authenticated execution safety</summary>

#### should preserve the selected boundary for authenticated execution safety

- should preserve the selected boundary for authenticated execution safety


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for authenticated execution safety")
step_launch_from_filesystem()
check_simpleos_filesystem_exec("NFR-006", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for authenticated execution safety</summary>

#### should reject missing stale substituted or invalid evidence for authenticated execution safety

- should reject missing stale substituted or invalid evidence for authenticated execution safety


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for authenticated execution safety")
step_launch_from_filesystem()
check_simpleos_filesystem_exec("NFR-006", "rejection")
```

</details>


</details>

### NFR-011: recovery and durability

#### should accept complete live evidence for recovery and durability

- should accept complete live evidence for recovery and durability
   - Artifact capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should accept complete live evidence for recovery and durability")
step_mount_filesystem()
check_simpleos_filesystem_conformance("NFR-011", "happy")
```

</details>

<details>
<summary>Advanced: should preserve the selected boundary for recovery and durability</summary>

#### should preserve the selected boundary for recovery and durability

- should preserve the selected boundary for recovery and durability


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the selected boundary for recovery and durability")
step_mount_filesystem()
check_simpleos_filesystem_conformance("NFR-011", "boundary")
```

</details>


</details>

<details>
<summary>Advanced: should reject missing stale substituted or invalid evidence for recovery and durability</summary>

#### should reject missing stale substituted or invalid evidence for recovery and durability

- should reject missing stale substituted or invalid evidence for recovery and durability


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject missing stale substituted or invalid evidence for recovery and durability")
step_mount_filesystem()
check_simpleos_filesystem_conformance("NFR-011", "rejection")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-002`
- `REQ-003`
- `REQ-004`
- `REQ-005`
- `REQ-006`
- `REQ-007`
- `REQ-008`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e21598eca670fb2dbb39e2a24d3f5093809e5fd54c49ea75f46ae4181f8fbbe7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e21598eca670fb2dbb39e2a24d3f5093809e5fd54c49ea75f46ae4181f8fbbe7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e21598eca670fb2dbb39e2a24d3f5093809e5fd54c49ea75f46ae4181f8fbbe7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_arch_fs_exec_spec.spl
mirror: doc/06_spec/03_system/os/simpleos/feature/simpleos_complete_os_hardening_arch_fs_exec_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/03_system/os/simpleos/feature/simpleos_complete_os_hardening_arch_fs_exec_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/simpleos/feature/simpleos_complete_os_hardening_arch_fs_exec_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_arch_fs_exec_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_arch_fs_exec_spec.spl:34:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept complete live evidence for three-architecture system execution' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_arch_fs_exec_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should accept complete live evidence for three-architecture system execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_arch_fs_exec_spec.spl:41:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the selected boundary for three-architecture system execution' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_arch_fs_exec_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve the selected boundary for three-architecture system execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_arch_fs_exec_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing stale substituted or invalid evidence for three-architecture system execution' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_arch_fs_exec_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject missing stale substituted or invalid evidence for three-architecture system execution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_arch_fs_exec_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should accept complete live evidence for shared filesystem contract' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_arch_fs_exec_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the selected boundary for shared filesystem contract' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_arch_fs_exec_spec.spl:70:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject missing stale substituted or invalid evidence for shared filesystem contract' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
