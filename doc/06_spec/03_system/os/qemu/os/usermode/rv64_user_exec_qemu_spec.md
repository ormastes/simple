# Rv64 User Exec Qemu Specification

> Tests covering RV64 User-Mode Execution.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rv64 User Exec Qemu Specification

## Scenarios

### RV64 User-Mode Execution

<details>
<summary>Advanced: trap vector installed</summary>

#### trap vector installed _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- trap vector installed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("trap vector installed")
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("trap vector installed")
```

</details>


</details>

<details>
<summary>Advanced: trap runtime installed</summary>

#### trap runtime installed _(slow)_

- trap runtime installed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("trap runtime installed")
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("trap runtime installed")
```

</details>


</details>

<details>
<summary>Advanced: user task spawned from proof binary</summary>

#### user task spawned from proof binary _(slow)_

- user task spawned from proof binary


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("user task spawned from proof binary")
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("spawned user task")
```

</details>


</details>

<details>
<summary>Advanced: entering U-mode at correct entry point</summary>

#### entering U-mode at correct entry point _(slow)_

- entering U-mode at correct entry point


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("entering U-mode at correct entry point")
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("entering U-mode")
```

</details>


</details>

<details>
<summary>Advanced: user debug_write syscall produces serial output</summary>

#### user debug_write syscall produces serial output _(slow)_

- user debug_write syscall produces serial output
   - Expected: verify_qemu_formal_output(ARCH, output).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("user debug_write syscall produces serial output")
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("P")
    expect(verify_qemu_formal_output(ARCH, output).is_ok()).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: boot sequence completes after user task</summary>

#### boot sequence completes after user task _(slow)_

- boot sequence completes after user task


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boot sequence completes after user task")
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
| Source | `test/03_system/os/qemu/os/usermode/rv64_user_exec_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RV64 User-Mode Execution.
- RV64 User-Mode Execution

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 6 |
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

- Canonical SPipe generation for source `c0760a10eaea5bef23a6f596147cae6ba9fb1dc4eddc5060bfb991ff9069e48c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c0760a10eaea5bef23a6f596147cae6ba9fb1dc4eddc5060bfb991ff9069e48c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c0760a10eaea5bef23a6f596147cae6ba9fb1dc4eddc5060bfb991ff9069e48c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/os/qemu/os/usermode/rv64_user_exec_qemu_spec.spl
mirror: doc/06_spec/03_system/os/qemu/os/usermode/rv64_user_exec_qemu_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/os/usermode/rv64_user_exec_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/os/usermode/rv64_user_exec_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/os/usermode/rv64_user_exec_qemu_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trap vector installed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/usermode/rv64_user_exec_qemu_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'trap runtime installed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/usermode/rv64_user_exec_qemu_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'user task spawned from proof binary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
