# Riscv64 Boot Qemu Specification

> Tests covering RISC-V 64 Architecture Boot.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv64 Boot Qemu Specification

## Scenarios

### RISC-V 64 Architecture Boot

<details>
<summary>Advanced: UART initialized via SBI</summary>

#### UART initialized via SBI _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- UART initialized via SBI


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("UART initialized via SBI")
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("UART")
```

</details>


</details>

<details>
<summary>Advanced: prints RISC-V 64 architecture identifier</summary>

#### prints RISC-V 64 architecture identifier _(slow)_

- prints RISC-V 64 architecture identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prints RISC-V 64 architecture identifier")
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("RISC-V 64")
```

</details>


</details>

<details>
<summary>Advanced: memory map parsed</summary>

#### memory map parsed _(slow)_

- memory map parsed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("memory map parsed")
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("Memory map")
```

</details>


</details>

<details>
<summary>Advanced: OpenSBI S-mode entry</summary>

#### OpenSBI S-mode entry _(slow)_

- OpenSBI S-mode entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("OpenSBI S-mode entry")
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("SBI")
```

</details>


</details>

<details>
<summary>Advanced: boot sequence completes</summary>

#### boot sequence completes _(slow)_

- boot sequence completes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boot sequence completes")
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("boot complete")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/boot/riscv64_boot_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RISC-V 64 Architecture Boot.
- RISC-V 64 Architecture Boot

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
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

- Canonical SPipe generation for source `de17d9915571b954b5828d764dcda546744b011e36994a36d0ddc395fe1a32be`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `de17d9915571b954b5828d764dcda546744b011e36994a36d0ddc395fe1a32be`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `de17d9915571b954b5828d764dcda546744b011e36994a36d0ddc395fe1a32be`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/qemu/os/boot/riscv64_boot_qemu_spec.spl
mirror: doc/06_spec/03_system/os/qemu/os/boot/riscv64_boot_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/os/boot/riscv64_boot_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/os/boot/riscv64_boot_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/os/boot/riscv64_boot_qemu_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'UART initialized via SBI' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/boot/riscv64_boot_qemu_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints RISC-V 64 architecture identifier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/boot/riscv64_boot_qemu_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'memory map parsed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
