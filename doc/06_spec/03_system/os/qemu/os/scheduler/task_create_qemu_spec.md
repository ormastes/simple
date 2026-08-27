# Task Create Qemu Specification

> Tests covering Task Creation ARM64, Task Creation x86_64, Task Creation RISC-V 32, Task Creation RISC-V 64.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Task Create Qemu Specification

## Scenarios

### Task Creation ARM64

<details>
<summary>Advanced: creates high-priority compute task</summary>

#### creates high-priority compute task _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates high-priority compute task


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates high-priority compute task")
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("Task A")
```

</details>


</details>

<details>
<summary>Advanced: creates normal-priority IPC tasks</summary>

#### creates normal-priority IPC tasks _(slow)_

- creates normal-priority IPC tasks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates normal-priority IPC tasks")
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("Task B")
```

</details>


</details>

<details>
<summary>Advanced: reports task creation pass</summary>

#### reports task creation pass _(slow)_

- reports task creation pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports task creation pass")
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("[PASS] task_creation")
```

</details>


</details>

### Task Creation x86_64

<details>
<summary>Advanced: creates high-priority compute task</summary>

#### creates high-priority compute task _(slow)_

- creates high-priority compute task


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates high-priority compute task")
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("Task A")
```

</details>


</details>

<details>
<summary>Advanced: creates normal-priority IPC tasks</summary>

#### creates normal-priority IPC tasks _(slow)_

- creates normal-priority IPC tasks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates normal-priority IPC tasks")
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("Task B")
```

</details>


</details>

<details>
<summary>Advanced: reports task creation pass</summary>

#### reports task creation pass _(slow)_

- reports task creation pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports task creation pass")
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("[PASS] task_creation")
```

</details>


</details>

### Task Creation RISC-V 32

<details>
<summary>Advanced: creates high-priority compute task</summary>

#### creates high-priority compute task _(slow)_

- creates high-priority compute task


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates high-priority compute task")
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("Task A")
```

</details>


</details>

<details>
<summary>Advanced: creates normal-priority IPC tasks</summary>

#### creates normal-priority IPC tasks _(slow)_

- creates normal-priority IPC tasks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates normal-priority IPC tasks")
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("Task B")
```

</details>


</details>

<details>
<summary>Advanced: reports task creation pass</summary>

#### reports task creation pass _(slow)_

- reports task creation pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports task creation pass")
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("[PASS] task_creation")
```

</details>


</details>

### Task Creation RISC-V 64

<details>
<summary>Advanced: creates high-priority compute task</summary>

#### creates high-priority compute task _(slow)_

- creates high-priority compute task


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates high-priority compute task")
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("Task A")
```

</details>


</details>

<details>
<summary>Advanced: creates normal-priority IPC tasks</summary>

#### creates normal-priority IPC tasks _(slow)_

- creates normal-priority IPC tasks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates normal-priority IPC tasks")
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("Task B")
```

</details>


</details>

<details>
<summary>Advanced: reports task creation pass</summary>

#### reports task creation pass _(slow)_

- reports task creation pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports task creation pass")
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("[PASS] task_creation")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/scheduler/task_create_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Task Creation ARM64, Task Creation x86_64, Task Creation RISC-V 32, Task Creation RISC-V 64.
- Task Creation ARM64
- Task Creation x86_64
- Task Creation RISC-V 32
- Task Creation RISC-V 64

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 12 |
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

- Canonical SPipe generation for source `a46bf333f22b75c931628a7ff15137c5a6d46c5d502c9740fce7164ccb4cbf49`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a46bf333f22b75c931628a7ff15137c5a6d46c5d502c9740fce7164ccb4cbf49`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a46bf333f22b75c931628a7ff15137c5a6d46c5d502c9740fce7164ccb4cbf49`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/qemu/os/scheduler/task_create_qemu_spec.spl
mirror: doc/06_spec/03_system/os/qemu/os/scheduler/task_create_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/os/scheduler/task_create_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/os/scheduler/task_create_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/os/scheduler/task_create_qemu_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates high-priority compute task' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/scheduler/task_create_qemu_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates normal-priority IPC tasks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/scheduler/task_create_qemu_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports task creation pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
