# Context Switch Qemu Specification

> Tests covering Context Switch ARM64, Context Switch x86_64, Context Switch RISC-V 32, Context Switch RISC-V 64.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context Switch Qemu Specification

## Scenarios

### Context Switch ARM64

<details>
<summary>Advanced: scheduler creates demo tasks</summary>

#### scheduler creates demo tasks _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- scheduler creates demo tasks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("scheduler creates demo tasks")
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("[SCHED] Creating demo tasks")
```

</details>


</details>

<details>
<summary>Advanced: all tasks registered successfully</summary>

#### all tasks registered successfully _(slow)_

- all tasks registered successfully


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all tasks registered successfully")
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("All demo tasks registered")
```

</details>


</details>

### Context Switch x86_64

<details>
<summary>Advanced: scheduler creates demo tasks</summary>

#### scheduler creates demo tasks _(slow)_

- scheduler creates demo tasks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("scheduler creates demo tasks")
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("[SCHED] Creating demo tasks")
```

</details>


</details>

<details>
<summary>Advanced: all tasks registered successfully</summary>

#### all tasks registered successfully _(slow)_

- all tasks registered successfully


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all tasks registered successfully")
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("All demo tasks registered")
```

</details>


</details>

### Context Switch RISC-V 32

<details>
<summary>Advanced: scheduler creates demo tasks</summary>

#### scheduler creates demo tasks _(slow)_

- scheduler creates demo tasks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("scheduler creates demo tasks")
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("[SCHED] Creating demo tasks")
```

</details>


</details>

<details>
<summary>Advanced: all tasks registered successfully</summary>

#### all tasks registered successfully _(slow)_

- all tasks registered successfully


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all tasks registered successfully")
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("All demo tasks registered")
```

</details>


</details>

### Context Switch RISC-V 64

<details>
<summary>Advanced: scheduler creates demo tasks</summary>

#### scheduler creates demo tasks _(slow)_

- scheduler creates demo tasks


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("scheduler creates demo tasks")
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("[SCHED] Creating demo tasks")
```

</details>


</details>

<details>
<summary>Advanced: all tasks registered successfully</summary>

#### all tasks registered successfully _(slow)_

- all tasks registered successfully


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all tasks registered successfully")
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
| Source | `test/03_system/os/qemu/os/scheduler/context_switch_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Context Switch ARM64, Context Switch x86_64, Context Switch RISC-V 32, Context Switch RISC-V 64.
- Context Switch ARM64
- Context Switch x86_64
- Context Switch RISC-V 32
- Context Switch RISC-V 64

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

- Canonical SPipe generation for source `32b492d83f8dfa6323d59bc5e530788f797908613b8d1488583bea40561a0068`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `32b492d83f8dfa6323d59bc5e530788f797908613b8d1488583bea40561a0068`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `32b492d83f8dfa6323d59bc5e530788f797908613b8d1488583bea40561a0068`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/qemu/os/scheduler/context_switch_qemu_spec.spl
mirror: doc/06_spec/03_system/os/qemu/os/scheduler/context_switch_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/os/scheduler/context_switch_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/os/scheduler/context_switch_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/os/scheduler/context_switch_qemu_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scheduler creates demo tasks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/scheduler/context_switch_qemu_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all tasks registered successfully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/scheduler/context_switch_qemu_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'scheduler creates demo tasks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
