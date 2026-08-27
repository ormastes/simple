# Memory Cross Qemu Specification

> Tests covering Memory Cross-Architecture Consistency.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Memory Cross Qemu Specification

## Scenarios

### Memory Cross-Architecture Consistency

<details>
<summary>Advanced: all architectures initialize PMM</summary>

#### all architectures initialize PMM _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


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
<summary>Advanced: all architectures report memory initialized</summary>

#### all architectures report memory initialized _(slow)_

- all architectures report memory initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all architectures report memory initialized")
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("Memory initialized")
```

</details>


</details>

<details>
<summary>Advanced: all architectures complete memory init pass</summary>

#### all architectures complete memory init pass _(slow)_

- all architectures complete memory init pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all architectures complete memory init pass")
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("[PASS] memory_init")
```

</details>


</details>

<details>
<summary>Advanced: all architectures report usable memory regions</summary>

#### all architectures report usable memory regions _(slow)_

- all architectures report usable memory regions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("all architectures report usable memory regions")
val arches = [Architecture.Arm64, Architecture.X86_64, Architecture.Riscv32, Architecture.Riscv64]
for arch in arches:
    if _can_run(arch):
        val output = _run_qemu(arch)
        expect(output).to_contain("usable")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/memory/memory_cross_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Memory Cross-Architecture Consistency.
- Memory Cross-Architecture Consistency

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

- Canonical SPipe generation for source `1d5070df4c22b375591aa38a1a1135c6e3f6eba4d496403534b7fb4efda201c4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1d5070df4c22b375591aa38a1a1135c6e3f6eba4d496403534b7fb4efda201c4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1d5070df4c22b375591aa38a1a1135c6e3f6eba4d496403534b7fb4efda201c4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/qemu/os/memory/memory_cross_qemu_spec.spl
mirror: doc/06_spec/03_system/os/qemu/os/memory/memory_cross_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/os/memory/memory_cross_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/os/memory/memory_cross_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/os/memory/memory_cross_qemu_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all architectures initialize PMM' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/memory/memory_cross_qemu_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all architectures report memory initialized' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/memory/memory_cross_qemu_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'all architectures complete memory init pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
