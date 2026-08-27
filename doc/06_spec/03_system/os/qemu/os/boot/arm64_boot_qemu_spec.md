# Arm64 Boot Qemu Specification

> Tests covering ARM64 Architecture Boot.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arm64 Boot Qemu Specification

## Scenarios

### ARM64 Architecture Boot

<details>
<summary>Advanced: PL011 UART initialized at 0x09000000</summary>

#### PL011 UART initialized at 0x09000000 _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- PL011 UART initialized at 0x09000000


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("PL011 UART initialized at 0x09000000")
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("PL011")
```

</details>


</details>

<details>
<summary>Advanced: prints ARM64 architecture identifier</summary>

#### prints ARM64 architecture identifier _(slow)_

- prints ARM64 architecture identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prints ARM64 architecture identifier")
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("ARM64")
```

</details>


</details>

<details>
<summary>Advanced: QEMU virt machine memory map detected</summary>

#### QEMU virt machine memory map detected _(slow)_

- QEMU virt machine memory map detected


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("QEMU virt machine memory map detected")
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("Memory map parsed")
```

</details>


</details>

<details>
<summary>Advanced: kernel region at 0x40000000</summary>

#### kernel region at 0x40000000 _(slow)_

- kernel region at 0x40000000


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("kernel region at 0x40000000")
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("0x40000000")
```

</details>


</details>

<details>
<summary>Advanced: GICv2 region reserved</summary>

#### GICv2 region reserved _(slow)_

- GICv2 region reserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("GICv2 region reserved")
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("device")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/boot/arm64_boot_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ARM64 Architecture Boot.
- ARM64 Architecture Boot

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

- Canonical SPipe generation for source `db5953e533eda1b6614505b13fe0369921a07b4fee20a30fa2bc5597165ac06a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db5953e533eda1b6614505b13fe0369921a07b4fee20a30fa2bc5597165ac06a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db5953e533eda1b6614505b13fe0369921a07b4fee20a30fa2bc5597165ac06a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/qemu/os/boot/arm64_boot_qemu_spec.spl
mirror: doc/06_spec/03_system/os/qemu/os/boot/arm64_boot_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/os/boot/arm64_boot_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/os/boot/arm64_boot_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/os/boot/arm64_boot_qemu_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PL011 UART initialized at 0x09000000' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/boot/arm64_boot_qemu_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints ARM64 architecture identifier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/boot/arm64_boot_qemu_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'QEMU virt machine memory map detected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
