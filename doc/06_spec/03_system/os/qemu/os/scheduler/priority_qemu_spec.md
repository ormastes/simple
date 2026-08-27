# Priority Qemu Specification

> Tests covering Priority Scheduling ARM64, Priority Scheduling x86_64, Priority Scheduling RISC-V 32, Priority Scheduling RISC-V 64.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Priority Qemu Specification

## Scenarios

### Priority Scheduling ARM64

<details>
<summary>Advanced: high-priority task (A) registered</summary>

#### high-priority task (A) registered _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- high-priority task (A) registered


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("high-priority task (A) registered")
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("priority=HIGH")
```

</details>


</details>

<details>
<summary>Advanced: normal-priority tasks (B, C) registered</summary>

#### normal-priority tasks (B, C) registered _(slow)_

- normal-priority tasks (B, C) registered


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normal-priority tasks (B, C) registered")
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("priority=NORMAL")
```

</details>


</details>

### Priority Scheduling x86_64

<details>
<summary>Advanced: high-priority task (A) registered</summary>

#### high-priority task (A) registered _(slow)_

- high-priority task (A) registered


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("high-priority task (A) registered")
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("priority=HIGH")
```

</details>


</details>

<details>
<summary>Advanced: normal-priority tasks (B, C) registered</summary>

#### normal-priority tasks (B, C) registered _(slow)_

- normal-priority tasks (B, C) registered


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normal-priority tasks (B, C) registered")
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("priority=NORMAL")
```

</details>


</details>

### Priority Scheduling RISC-V 32

<details>
<summary>Advanced: high-priority task (A) registered</summary>

#### high-priority task (A) registered _(slow)_

- high-priority task (A) registered


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("high-priority task (A) registered")
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("priority=HIGH")
```

</details>


</details>

<details>
<summary>Advanced: normal-priority tasks (B, C) registered</summary>

#### normal-priority tasks (B, C) registered _(slow)_

- normal-priority tasks (B, C) registered


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normal-priority tasks (B, C) registered")
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("priority=NORMAL")
```

</details>


</details>

### Priority Scheduling RISC-V 64

<details>
<summary>Advanced: high-priority task (A) registered</summary>

#### high-priority task (A) registered _(slow)_

- high-priority task (A) registered


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("high-priority task (A) registered")
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("priority=HIGH")
```

</details>


</details>

<details>
<summary>Advanced: normal-priority tasks (B, C) registered</summary>

#### normal-priority tasks (B, C) registered _(slow)_

- normal-priority tasks (B, C) registered


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("normal-priority tasks (B, C) registered")
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("priority=NORMAL")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/scheduler/priority_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Priority Scheduling ARM64, Priority Scheduling x86_64, Priority Scheduling RISC-V 32, Priority Scheduling RISC-V 64.
- Priority Scheduling ARM64
- Priority Scheduling x86_64
- Priority Scheduling RISC-V 32
- Priority Scheduling RISC-V 64

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

- Canonical SPipe generation for source `5f5e21662f84ac7a6c9f0b3c23bc0e80e89c07e43b68e8d29a02f69946ef411f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5f5e21662f84ac7a6c9f0b3c23bc0e80e89c07e43b68e8d29a02f69946ef411f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5f5e21662f84ac7a6c9f0b3c23bc0e80e89c07e43b68e8d29a02f69946ef411f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/qemu/os/scheduler/priority_qemu_spec.spl
mirror: doc/06_spec/03_system/os/qemu/os/scheduler/priority_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/os/scheduler/priority_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/os/scheduler/priority_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/os/scheduler/priority_qemu_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'high-priority task (A) registered' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/scheduler/priority_qemu_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'normal-priority tasks (B, C) registered' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/scheduler/priority_qemu_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'high-priority task (A) registered' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
