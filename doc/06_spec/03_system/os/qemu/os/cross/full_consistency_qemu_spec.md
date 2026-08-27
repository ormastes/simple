# Full Consistency Qemu Specification

> Tests covering Full Cross-Architecture Consistency.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Full Consistency Qemu Specification

## Scenarios

### Full Cross-Architecture Consistency

<details>
<summary>Advanced: all architectures print SimpleOS banner</summary>

#### all architectures print SimpleOS banner _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- all architectures print SimpleOS banner


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all architectures print SimpleOS banner")
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("SimpleOS")
```

</details>


</details>

<details>
<summary>Advanced: all architectures initialize PMM</summary>

#### all architectures initialize PMM _(slow)_

- all architectures initialize PMM


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all architectures initialize PMM")
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("[PMM]")
```

</details>


</details>

<details>
<summary>Advanced: all architectures initialize interrupts</summary>

#### all architectures initialize interrupts _(slow)_

- all architectures initialize interrupts


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all architectures initialize interrupts")
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("[IRQ]")
```

</details>


</details>

<details>
<summary>Advanced: all architectures initialize timer</summary>

#### all architectures initialize timer _(slow)_

- all architectures initialize timer


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all architectures initialize timer")
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("[TIMER]")
```

</details>


</details>

<details>
<summary>Advanced: all architectures create scheduler tasks</summary>

#### all architectures create scheduler tasks _(slow)_

- all architectures create scheduler tasks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all architectures create scheduler tasks")
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("[SCHED]")
```

</details>


</details>

<details>
<summary>Advanced: all architectures pass 5 boot tests</summary>

#### all architectures pass 5 boot tests _(slow)_

- all architectures pass 5 boot tests


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all architectures pass 5 boot tests")
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("passed=5 failed=0")
```

</details>


</details>

<details>
<summary>Advanced: all architectures complete test suite</summary>

#### all architectures complete test suite _(slow)_

- all architectures complete test suite


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all architectures complete test suite")
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("SimpleOS Tests Complete")
```

</details>


</details>

<details>
<summary>Advanced: no architecture reports failures</summary>

#### no architecture reports failures _(slow)_

- no architecture reports failures
   - Expected: has_fail is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("no architecture reports failures")
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        val has_fail = output.contains("[FAIL]")
        expect(has_fail).to_equal(false)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/cross/full_consistency_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Full Cross-Architecture Consistency.
- Full Cross-Architecture Consistency

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

- Canonical SPipe generation for source `a0484db03efb289378472e9d83658d6fd39ec3e39d78338323ab946a5a9df276`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a0484db03efb289378472e9d83658d6fd39ec3e39d78338323ab946a5a9df276`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a0484db03efb289378472e9d83658d6fd39ec3e39d78338323ab946a5a9df276`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/qemu/os/cross/full_consistency_qemu_spec.spl
mirror: doc/06_spec/03_system/os/qemu/os/cross/full_consistency_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/os/cross/full_consistency_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/os/cross/full_consistency_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/os/cross/full_consistency_qemu_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all architectures print SimpleOS banner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/cross/full_consistency_qemu_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all architectures initialize PMM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/cross/full_consistency_qemu_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all architectures initialize interrupts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
