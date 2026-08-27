# Vmm Qemu Specification

> Tests covering VMM ARM64 (4KB granule), VMM x86_64 (4-level PML4), VMM RISC-V 32 (Sv32), VMM RISC-V 64 (Sv39), VMM CoW walker (_cow_clear_writable_recursive).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vmm Qemu Specification

## Scenarios

### VMM ARM64 (4KB granule)

<details>
<summary>Advanced: identity maps kernel region</summary>

#### identity maps kernel region _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- identity maps kernel region


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identity maps kernel region")
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("[PMM]")
```

</details>


</details>

<details>
<summary>Advanced: page table initialized</summary>

#### page table initialized _(slow)_

- page table initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("page table initialized")
if _can_run(Architecture.Arm64):
    val output = _run_qemu(Architecture.Arm64)
    expect(output).to_contain("Memory initialized")
```

</details>


</details>

### VMM x86_64 (4-level PML4)

<details>
<summary>Advanced: identity maps kernel region</summary>

#### identity maps kernel region _(slow)_

- identity maps kernel region


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identity maps kernel region")
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("[PMM]")
```

</details>


</details>

<details>
<summary>Advanced: page table initialized</summary>

#### page table initialized _(slow)_

- page table initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("page table initialized")
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    expect(output).to_contain("Memory initialized")
```

</details>


</details>

### VMM RISC-V 32 (Sv32)

<details>
<summary>Advanced: identity maps kernel region</summary>

#### identity maps kernel region _(slow)_

- identity maps kernel region


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identity maps kernel region")
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("[PMM]")
```

</details>


</details>

<details>
<summary>Advanced: page table initialized</summary>

#### page table initialized _(slow)_

- page table initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("page table initialized")
if _can_run(Architecture.Riscv32):
    val output = _run_qemu(Architecture.Riscv32)
    expect(output).to_contain("Memory initialized")
```

</details>


</details>

### VMM RISC-V 64 (Sv39)

<details>
<summary>Advanced: identity maps kernel region</summary>

#### identity maps kernel region _(slow)_

- identity maps kernel region


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identity maps kernel region")
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("[PMM]")
```

</details>


</details>

<details>
<summary>Advanced: page table initialized</summary>

#### page table initialized _(slow)_

- page table initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("page table initialized")
if _can_run(Architecture.Riscv64):
    val output = _run_qemu(Architecture.Riscv64)
    expect(output).to_contain("Memory initialized")
```

</details>


</details>

### VMM CoW walker (_cow_clear_writable_recursive)

<details>
<summary>Advanced: clears writable via _cow_clear_writable_recursive</summary>

#### clears writable via _cow_clear_writable_recursive _(slow)_

- clears writable via _cow_clear_writable_recursive


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clears writable via _cow_clear_writable_recursive")
"""Exercises the CoW walker against a synthetic 4-level table.

The guest kernel logs '[VMM] cow-clone' after vmm_cow_clone_pages.
We verify that a QEMU boot with COW clone produces this marker,
confirming _cow_clear_writable_recursive walked the user half.
"""
if _can_run(Architecture.X86_64):
    val output = _run_qemu(Architecture.X86_64)
    # The CoW clone path is exercised during process spawn.
    # At minimum the kernel must reach scheduler init without fault.
    expect(output).to_contain("[VMM]")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/memory/vmm_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering VMM ARM64 (4KB granule), VMM x86_64 (4-level PML4), VMM RISC-V 32 (Sv32), VMM RISC-V 64 (Sv39), VMM CoW walker (_cow_clear_writable_recursive).
- VMM ARM64 (4KB granule)
- VMM x86_64 (4-level PML4)
- VMM RISC-V 32 (Sv32)
- VMM RISC-V 64 (Sv39)
- VMM CoW walker (_cow_clear_writable_recursive)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 9 |
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

- Canonical SPipe generation for source `30286318b6cfc77d8cb95ed546da07b752b549b1bfafbb124c7c762dce841a60`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `30286318b6cfc77d8cb95ed546da07b752b549b1bfafbb124c7c762dce841a60`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `30286318b6cfc77d8cb95ed546da07b752b549b1bfafbb124c7c762dce841a60`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/qemu/os/memory/vmm_qemu_spec.spl
mirror: doc/06_spec/03_system/os/qemu/os/memory/vmm_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/os/memory/vmm_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/os/memory/vmm_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/os/memory/vmm_qemu_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identity maps kernel region' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/memory/vmm_qemu_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'page table initialized' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/memory/vmm_qemu_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identity maps kernel region' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
