# Software Int Qemu Specification

> Tests covering Software Interrupts ARM64 (SVC), Software Interrupts x86_64 (INT/SYSCALL), Software Interrupts RISC-V 32 (ECALL), Software Interrupts RISC-V 64 (ECALL).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Software Int Qemu Specification

## Scenarios

### Software Interrupts ARM64 (SVC)

<details>
<summary>Advanced: interrupt subsystem initializes</summary>

#### interrupt subsystem initializes _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- interrupt subsystem initializes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interrupt subsystem initializes")
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("[IRQ]")
```

</details>


</details>

<details>
<summary>Advanced: reports interrupt init pass</summary>

#### reports interrupt init pass _(slow)_

- reports interrupt init pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports interrupt init pass")
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("[PASS] interrupt_init")
```

</details>


</details>

### Software Interrupts x86_64 (INT/SYSCALL)

<details>
<summary>Advanced: interrupt subsystem initializes</summary>

#### interrupt subsystem initializes _(slow)_

- interrupt subsystem initializes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interrupt subsystem initializes")
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("[IRQ]")
```

</details>


</details>

<details>
<summary>Advanced: reports interrupt init pass</summary>

#### reports interrupt init pass _(slow)_

- reports interrupt init pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports interrupt init pass")
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("[PASS] interrupt_init")
```

</details>


</details>

### Software Interrupts RISC-V 32 (ECALL)

<details>
<summary>Advanced: interrupt subsystem initializes</summary>

#### interrupt subsystem initializes _(slow)_

- interrupt subsystem initializes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interrupt subsystem initializes")
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("[IRQ]")
```

</details>


</details>

<details>
<summary>Advanced: reports interrupt init pass</summary>

#### reports interrupt init pass _(slow)_

- reports interrupt init pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports interrupt init pass")
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("[PASS] interrupt_init")
```

</details>


</details>

### Software Interrupts RISC-V 64 (ECALL)

<details>
<summary>Advanced: interrupt subsystem initializes</summary>

#### interrupt subsystem initializes _(slow)_

- interrupt subsystem initializes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("interrupt subsystem initializes")
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("[IRQ]")
```

</details>


</details>

<details>
<summary>Advanced: reports interrupt init pass</summary>

#### reports interrupt init pass _(slow)_

- reports interrupt init pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports interrupt init pass")
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("[PASS] interrupt_init")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/interrupts/software_int_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Software Interrupts ARM64 (SVC), Software Interrupts x86_64 (INT/SYSCALL), Software Interrupts RISC-V 32 (ECALL), Software Interrupts RISC-V 64 (ECALL).
- Software Interrupts ARM64 (SVC)
- Software Interrupts x86_64 (INT/SYSCALL)
- Software Interrupts RISC-V 32 (ECALL)
- Software Interrupts RISC-V 64 (ECALL)

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

- Canonical SPipe generation for source `1f182c1b295639f37159520dd663b1a1b9d8413dc9ed3013814fbc10a8174ef7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1f182c1b295639f37159520dd663b1a1b9d8413dc9ed3013814fbc10a8174ef7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1f182c1b295639f37159520dd663b1a1b9d8413dc9ed3013814fbc10a8174ef7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/qemu/os/interrupts/software_int_qemu_spec.spl
mirror: doc/06_spec/03_system/os/qemu/os/interrupts/software_int_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/os/interrupts/software_int_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/os/interrupts/software_int_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/os/interrupts/software_int_qemu_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'interrupt subsystem initializes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/interrupts/software_int_qemu_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports interrupt init pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/interrupts/software_int_qemu_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'interrupt subsystem initializes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
