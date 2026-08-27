# Serial Input Qemu Specification

> Tests covering Serial Input ARM64, Serial Input x86_64, Serial Input RISC-V 32, Serial Input RISC-V 64.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serial Input Qemu Specification

## Scenarios

### Serial Input ARM64

<details>
<summary>Advanced: UART receive path initialized</summary>

#### UART receive path initialized _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- UART receive path initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("UART receive path initialized")
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

### Serial Input x86_64

<details>
<summary>Advanced: COM1 receive path initialized</summary>

#### COM1 receive path initialized _(slow)_

- COM1 receive path initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("COM1 receive path initialized")
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

### Serial Input RISC-V 32

<details>
<summary>Advanced: UART receive path initialized</summary>

#### UART receive path initialized _(slow)_

- UART receive path initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("UART receive path initialized")
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

### Serial Input RISC-V 64

<details>
<summary>Advanced: UART receive path initialized</summary>

#### UART receive path initialized _(slow)_

- UART receive path initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("UART receive path initialized")
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | I/O |
| Status | Active |
| Source | `test/03_system/os/qemu/os/io/serial_input_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Serial Input ARM64, Serial Input x86_64, Serial Input RISC-V 32, Serial Input RISC-V 64.
- Serial Input ARM64
- Serial Input x86_64
- Serial Input RISC-V 32
- Serial Input RISC-V 64

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
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

- Canonical SPipe generation for source `1d5b6effda6edc0ab98e19c73f9e34078e612f3183380281d3d6b081d2c33f8e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1d5b6effda6edc0ab98e19c73f9e34078e612f3183380281d3d6b081d2c33f8e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1d5b6effda6edc0ab98e19c73f9e34078e612f3183380281d3d6b081d2c33f8e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/qemu/os/io/serial_input_qemu_spec.spl
mirror: doc/06_spec/03_system/os/qemu/os/io/serial_input_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/os/io/serial_input_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/os/io/serial_input_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/os/io/serial_input_qemu_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'UART receive path initialized' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/io/serial_input_qemu_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'COM1 receive path initialized' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/io/serial_input_qemu_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'UART receive path initialized' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
