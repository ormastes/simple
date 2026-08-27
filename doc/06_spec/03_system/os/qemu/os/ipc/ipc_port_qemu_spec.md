# Ipc Port Qemu Specification

> Tests covering IPC Port ARM64, IPC Port x86_64, IPC Port x86_32, IPC Port RISC-V 32, IPC Port RISC-V 64.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc Port Qemu Specification

## Scenarios

### IPC Port ARM64

<details>
<summary>Advanced: IPC sender task created</summary>

#### IPC sender task created _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- IPC sender task created


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("IPC sender task created")
if _can_run(Architecture.Arm64):
    val output = _run_qemu_cached(Architecture.Arm64)
    expect(output).to_contain("[TASK]")
```

</details>


</details>

<details>
<summary>Advanced: IPC receiver task created</summary>

#### IPC receiver task created _(slow)_

- IPC receiver task created


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("IPC receiver task created")
if _can_run(Architecture.Arm64):
    val output = _run_qemu_cached(Architecture.Arm64)
    expect(output).to_contain("ipc_receiver")
```

</details>


</details>

### IPC Port x86_64

<details>
<summary>Advanced: IPC sender task created</summary>

#### IPC sender task created _(slow)_

- IPC sender task created


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("IPC sender task created")
if _can_run(Architecture.X86_64):
    val output = _run_qemu_cached(Architecture.X86_64)
    expect(output).to_contain("[TASK]")
```

</details>


</details>

<details>
<summary>Advanced: IPC receiver task created</summary>

#### IPC receiver task created _(slow)_

- IPC receiver task created


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("IPC receiver task created")
if _can_run(Architecture.X86_64):
    val output = _run_qemu_cached(Architecture.X86_64)
    expect(output).to_contain("ipc_receiver")
```

</details>


</details>

### IPC Port x86_32

<details>
<summary>Advanced: IPC sender task created</summary>

#### IPC sender task created _(slow)_

- IPC sender task created


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("IPC sender task created")
if _can_run(Architecture.X86):
    val output = _run_qemu_cached(Architecture.X86)
    expect(output).to_contain("[TASK]")
```

</details>


</details>

<details>
<summary>Advanced: IPC receiver task created</summary>

#### IPC receiver task created _(slow)_

- IPC receiver task created


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("IPC receiver task created")
if _can_run(Architecture.X86):
    val output = _run_qemu_cached(Architecture.X86)
    expect(output).to_contain("ipc_receiver")
```

</details>


</details>

### IPC Port RISC-V 32

<details>
<summary>Advanced: IPC sender task created</summary>

#### IPC sender task created _(slow)_

- IPC sender task created


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("IPC sender task created")
if _can_run(Architecture.Riscv32):
    val output = _run_qemu_cached(Architecture.Riscv32)
    expect(output).to_contain("[TASK]")
```

</details>


</details>

<details>
<summary>Advanced: IPC receiver task created</summary>

#### IPC receiver task created _(slow)_

- IPC receiver task created


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("IPC receiver task created")
if _can_run(Architecture.Riscv32):
    val output = _run_qemu_cached(Architecture.Riscv32)
    expect(output).to_contain("ipc_receiver")
```

</details>


</details>

### IPC Port RISC-V 64

<details>
<summary>Advanced: IPC sender task created</summary>

#### IPC sender task created _(slow)_

- IPC sender task created


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("IPC sender task created")
if _can_run(Architecture.Riscv64):
    val output = _run_qemu_cached(Architecture.Riscv64)
    expect(output).to_contain("[TASK]")
```

</details>


</details>

<details>
<summary>Advanced: IPC receiver task created</summary>

#### IPC receiver task created _(slow)_

- IPC receiver task created


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("IPC receiver task created")
if _can_run(Architecture.Riscv64):
    val output = _run_qemu_cached(Architecture.Riscv64)
    expect(output).to_contain("ipc_receiver")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/ipc/ipc_port_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering IPC Port ARM64, IPC Port x86_64, IPC Port x86_32, IPC Port RISC-V 32, IPC Port RISC-V 64.
- IPC Port ARM64
- IPC Port x86_64
- IPC Port x86_32
- IPC Port RISC-V 32
- IPC Port RISC-V 64

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 10 |
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

- Canonical SPipe generation for source `afadd668ae2af7b6b300e128fefb0e3cccee4f23179352be81c0a2410e67c4e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `afadd668ae2af7b6b300e128fefb0e3cccee4f23179352be81c0a2410e67c4e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `afadd668ae2af7b6b300e128fefb0e3cccee4f23179352be81c0a2410e67c4e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/qemu/os/ipc/ipc_port_qemu_spec.spl
mirror: doc/06_spec/03_system/os/qemu/os/ipc/ipc_port_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/os/ipc/ipc_port_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/os/ipc/ipc_port_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/os/ipc/ipc_port_qemu_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'IPC sender task created' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/ipc/ipc_port_qemu_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'IPC receiver task created' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/ipc/ipc_port_qemu_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'IPC sender task created' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
