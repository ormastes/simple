# Boot Smoke Qemu Specification

> Tests covering ARM64 Boot Smoke Tests, x86_64 Boot Smoke Tests, RISC-V 32 Boot Smoke Tests, RISC-V 64 Boot Smoke Tests.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Boot Smoke Qemu Specification

## Scenarios

### ARM64 Boot Smoke Tests

<details>
<summary>Advanced: boots and prints SimpleOS banner</summary>

#### boots and prints SimpleOS banner _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- boots and prints SimpleOS banner


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots and prints SimpleOS banner")
if _can_run(Architecture.Arm64):
    val output = run_qemu_for_arch(Architecture.Arm64)
    expect(output).to_contain("SimpleOS")
```

</details>


</details>

<details>
<summary>Advanced: initializes PL011 UART</summary>

#### initializes PL011 UART _(slow)_

- initializes PL011 UART


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("initializes PL011 UART")
if _can_run(Architecture.Arm64):
    val output = run_qemu_for_arch(Architecture.Arm64)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

<details>
<summary>Advanced: reports memory map</summary>

#### reports memory map _(slow)_

- reports memory map


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports memory map")
if _can_run(Architecture.Arm64):
    val output = run_qemu_for_arch(Architecture.Arm64)
    expect(output).to_contain("Memory map")
```

</details>


</details>

<details>
<summary>Advanced: completes boot sequence</summary>

#### completes boot sequence _(slow)_

- completes boot sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("completes boot sequence")
if _can_run(Architecture.Arm64):
    val output = run_qemu_for_arch(Architecture.Arm64)
    expect(output).to_contain("boot complete")
```

</details>


</details>

<details>
<summary>Advanced: passes all boot tests</summary>

#### passes all boot tests _(slow)_

- passes all boot tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes all boot tests")
if _can_run(Architecture.Arm64):
    val output = run_qemu_for_arch(Architecture.Arm64)
    expect(output).to_contain("[PASS] boot_and_init")
```

</details>


</details>

### x86_64 Boot Smoke Tests

<details>
<summary>Advanced: boots and prints SimpleOS banner</summary>

#### boots and prints SimpleOS banner _(slow)_

- boots and prints SimpleOS banner


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots and prints SimpleOS banner")
if _can_run(Architecture.X86_64):
    val output = run_qemu_for_arch(Architecture.X86_64)
    expect(output).to_contain("SimpleOS")
```

</details>


</details>

<details>
<summary>Advanced: initializes COM1 serial</summary>

#### initializes COM1 serial _(slow)_

- initializes COM1 serial


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("initializes COM1 serial")
if _can_run(Architecture.X86_64):
    val output = run_qemu_for_arch(Architecture.X86_64)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

<details>
<summary>Advanced: enumerates PCI devices</summary>

#### enumerates PCI devices _(slow)_

- enumerates PCI devices


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enumerates PCI devices")
if _can_run(Architecture.X86_64):
    val output = run_qemu_for_arch(Architecture.X86_64)
    expect(output).to_contain("[pcimgr]")
```

</details>


</details>

<details>
<summary>Advanced: completes boot sequence</summary>

#### completes boot sequence _(slow)_

- completes boot sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("completes boot sequence")
if _can_run(Architecture.X86_64):
    val output = run_qemu_for_arch(Architecture.X86_64)
    expect(output).to_contain("[stage1] PASS")
```

</details>


</details>

<details>
<summary>Advanced: passes all boot tests</summary>

#### passes all boot tests _(slow)_

- passes all boot tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes all boot tests")
if _can_run(Architecture.X86_64):
    val output = run_qemu_for_arch(Architecture.X86_64)
    expect(output).to_contain("TEST PASSED")
```

</details>


</details>

### RISC-V 32 Boot Smoke Tests

<details>
<summary>Advanced: boots and prints SimpleOS banner</summary>

#### boots and prints SimpleOS banner _(slow)_

- boots and prints SimpleOS banner


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots and prints SimpleOS banner")
if _can_run(Architecture.Riscv32):
    val output = run_qemu_for_arch(Architecture.Riscv32)
    expect(output).to_contain("SimpleOS")
```

</details>


</details>

<details>
<summary>Advanced: initializes UART via SBI</summary>

#### initializes UART via SBI _(slow)_

- initializes UART via SBI


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("initializes UART via SBI")
if _can_run(Architecture.Riscv32):
    val output = run_qemu_for_arch(Architecture.Riscv32)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

<details>
<summary>Advanced: reports memory map</summary>

#### reports memory map _(slow)_

- reports memory map


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports memory map")
if _can_run(Architecture.Riscv32):
    val output = run_qemu_for_arch(Architecture.Riscv32)
    expect(output).to_contain("Memory map")
```

</details>


</details>

<details>
<summary>Advanced: completes boot sequence</summary>

#### completes boot sequence _(slow)_

- completes boot sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("completes boot sequence")
if _can_run(Architecture.Riscv32):
    val output = run_qemu_for_arch(Architecture.Riscv32)
    expect(output).to_contain("boot complete")
```

</details>


</details>

<details>
<summary>Advanced: passes all boot tests</summary>

#### passes all boot tests _(slow)_

- passes all boot tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes all boot tests")
if _can_run(Architecture.Riscv32):
    val output = run_qemu_for_arch(Architecture.Riscv32)
    expect(output).to_contain("[PASS] boot_and_init")
```

</details>


</details>

### RISC-V 64 Boot Smoke Tests

<details>
<summary>Advanced: boots and prints SimpleOS banner</summary>

#### boots and prints SimpleOS banner _(slow)_

- boots and prints SimpleOS banner


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boots and prints SimpleOS banner")
if _can_run(Architecture.Riscv64):
    val output = run_qemu_for_arch(Architecture.Riscv64)
    expect(output).to_contain("SimpleOS")
```

</details>


</details>

<details>
<summary>Advanced: initializes UART via SBI</summary>

#### initializes UART via SBI _(slow)_

- initializes UART via SBI


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("initializes UART via SBI")
if _can_run(Architecture.Riscv64):
    val output = run_qemu_for_arch(Architecture.Riscv64)
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

<details>
<summary>Advanced: reports memory map</summary>

#### reports memory map _(slow)_

- reports memory map


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports memory map")
if _can_run(Architecture.Riscv64):
    val output = run_qemu_for_arch(Architecture.Riscv64)
    expect(output).to_contain("Memory map")
```

</details>


</details>

<details>
<summary>Advanced: completes boot sequence</summary>

#### completes boot sequence _(slow)_

- completes boot sequence


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("completes boot sequence")
if _can_run(Architecture.Riscv64):
    val output = run_qemu_for_arch(Architecture.Riscv64)
    expect(output).to_contain("boot complete")
```

</details>


</details>

<details>
<summary>Advanced: passes all boot tests</summary>

#### passes all boot tests _(slow)_

- passes all boot tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes all boot tests")
if _can_run(Architecture.Riscv64):
    val output = run_qemu_for_arch(Architecture.Riscv64)
    expect(output).to_contain("[PASS] boot_and_init")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/boot/boot_smoke_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ARM64 Boot Smoke Tests, x86_64 Boot Smoke Tests, RISC-V 32 Boot Smoke Tests, RISC-V 64 Boot Smoke Tests.
- ARM64 Boot Smoke Tests
- x86_64 Boot Smoke Tests
- RISC-V 32 Boot Smoke Tests
- RISC-V 64 Boot Smoke Tests

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 20 |
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

- Canonical SPipe generation for source `2caaa0bfa99591ef437f20c44371a124f8037cc5dcde4f1db2e212e7d28c119d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2caaa0bfa99591ef437f20c44371a124f8037cc5dcde4f1db2e212e7d28c119d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2caaa0bfa99591ef437f20c44371a124f8037cc5dcde4f1db2e212e7d28c119d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/qemu/os/boot/boot_smoke_qemu_spec.spl
mirror: doc/06_spec/03_system/os/qemu/os/boot/boot_smoke_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/os/boot/boot_smoke_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/os/boot/boot_smoke_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/os/boot/boot_smoke_qemu_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'boots and prints SimpleOS banner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/boot/boot_smoke_qemu_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'initializes PL011 UART' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/boot/boot_smoke_qemu_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports memory map' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
