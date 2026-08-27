# Ipc Capability Qemu Specification

> Tests covering Capability ARM64, Capability x86_64, Capability RISC-V 32, Capability RISC-V 64.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc Capability Qemu Specification

## Scenarios

### Capability ARM64

<details>
<summary>Advanced: kernel boots with IPC subsystem</summary>

#### kernel boots with IPC subsystem _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- kernel boots with IPC subsystem


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("kernel boots with IPC subsystem")
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("[SCHED]")
```

</details>


</details>

<details>
<summary>Advanced: all demo tasks registered</summary>

#### all demo tasks registered _(slow)_

- all demo tasks registered


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all demo tasks registered")
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("All demo tasks registered")
```

</details>


</details>

### Capability x86_64

<details>
<summary>Advanced: kernel boots with IPC subsystem</summary>

#### kernel boots with IPC subsystem _(slow)_

- kernel boots with IPC subsystem


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("kernel boots with IPC subsystem")
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("[SCHED]")
```

</details>


</details>

<details>
<summary>Advanced: all demo tasks registered</summary>

#### all demo tasks registered _(slow)_

- all demo tasks registered


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all demo tasks registered")
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("All demo tasks registered")
```

</details>


</details>

### Capability RISC-V 32

<details>
<summary>Advanced: kernel boots with IPC subsystem</summary>

#### kernel boots with IPC subsystem _(slow)_

- kernel boots with IPC subsystem


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("kernel boots with IPC subsystem")
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("[SCHED]")
```

</details>


</details>

<details>
<summary>Advanced: all demo tasks registered</summary>

#### all demo tasks registered _(slow)_

- all demo tasks registered


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all demo tasks registered")
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("All demo tasks registered")
```

</details>


</details>

### Capability RISC-V 64

<details>
<summary>Advanced: kernel boots with IPC subsystem</summary>

#### kernel boots with IPC subsystem _(slow)_

- kernel boots with IPC subsystem


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("kernel boots with IPC subsystem")
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("[SCHED]")
```

</details>


</details>

<details>
<summary>Advanced: all demo tasks registered</summary>

#### all demo tasks registered _(slow)_

- all demo tasks registered


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all demo tasks registered")
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("All demo tasks registered")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/ipc/ipc_capability_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Capability ARM64, Capability x86_64, Capability RISC-V 32, Capability RISC-V 64.
- Capability ARM64
- Capability x86_64
- Capability RISC-V 32
- Capability RISC-V 64

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 8 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9585630ecaf0cfe779b0947c96070f2e5cbc94dca06333102bc2b17ae1286985`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9585630ecaf0cfe779b0947c96070f2e5cbc94dca06333102bc2b17ae1286985`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9585630ecaf0cfe779b0947c96070f2e5cbc94dca06333102bc2b17ae1286985`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/qemu/os/ipc/ipc_capability_qemu_spec.spl
mirror: doc/06_spec/03_system/os/qemu/os/ipc/ipc_capability_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/os/ipc/ipc_capability_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/os/ipc/ipc_capability_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/os/ipc/ipc_capability_qemu_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'kernel boots with IPC subsystem' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/ipc/ipc_capability_qemu_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all demo tasks registered' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/ipc/ipc_capability_qemu_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'kernel boots with IPC subsystem' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
