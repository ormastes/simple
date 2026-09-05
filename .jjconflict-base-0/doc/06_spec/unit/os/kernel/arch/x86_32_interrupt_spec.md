# X86 32 Interrupt Specification

> Tests covering x86_32 interrupt runtime bridge.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 32 Interrupt Specification

## Scenarios

### x86_32 interrupt runtime bridge

#### fails cleanly before runtime installation

- fails cleanly before runtime installation
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails cleanly before runtime installation")
"""Dispatch should report missing runtime instead of fabricating success."""
val result = x86_32_dispatch_context(syscall_context(4u32))
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap()).to_contain("runtime is not installed")
```

</details>

#### installs runtime through the HAL wrapper

- installs runtime through the HAL wrapper
   - Expected: intr.runtime_installed() is true
   - Expected: x86_32_runtime_installed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("installs runtime through the HAL wrapper")
"""The x86_32 interrupt HAL owns runtime installation entrypoints."""
val intr = X86_32Interrupt()
intr.install_runtime(Scheduler.new(), IpcManager.new(), KernelLog.new(8))
expect(intr.runtime_installed()).to_equal(true)
expect(x86_32_runtime_installed()).to_equal(true)
```

</details>

#### dispatches getpid through a trapped context

- dispatches getpid through a trapped context
   - Expected: result.is_err() is false
   - Expected: updated.eax equals `0u32`
   - Expected: updated.eip equals `0x1002u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches getpid through a trapped context")
"""A successful syscall writes eax and advances eip past int 0x80."""
val intr = X86_32Interrupt()
intr.install_runtime(Scheduler.new(), IpcManager.new(), KernelLog.new(8))
val result = x86_32_dispatch_context(syscall_context(4u32))
expect(result.is_err()).to_equal(false)
val updated = result.unwrap()
expect(updated.eax).to_equal(0u32)
expect(updated.eip).to_equal(0x1002u32)
```

</details>

#### dispatches brk query through a trapped context

- dispatches brk query through a trapped context
   - Expected: result.is_err() is false
   - Expected: updated.eax equals `0x30000000u32`
   - Expected: updated.eip equals `0x1002u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches brk query through a trapped context")
"""The x86_32 bridge carries nontrivial process syscalls through int 0x80."""
brk_reset_for_test()
val intr = X86_32Interrupt()
intr.install_runtime(Scheduler.new(), IpcManager.new(), KernelLog.new(8))
val result = x86_32_dispatch_context(syscall_context(15u32))
expect(result.is_err()).to_equal(false)
val updated = result.unwrap()
expect(updated.eax).to_equal(0x30000000u32)
expect(updated.eip).to_equal(0x1002u32)
```

</details>

#### exposes a primitive ABI for future assembly stubs

- exposes a primitive ABI for future assembly stubs
   - Expected: x86_32_dispatch_installed_syscall_abi(4u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32) equals `0`
   - Expected: x86_32_dispatch_installed_syscall_abi(99u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32) equals `-38`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes a primitive ABI for future assembly stubs")
"""The ABI helper returns syscall results as signed i32 values."""
val intr = X86_32Interrupt()
intr.install_runtime(Scheduler.new(), IpcManager.new(), KernelLog.new(8))
expect(x86_32_dispatch_installed_syscall_abi(4u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32)).to_equal(0)
expect(x86_32_dispatch_installed_syscall_abi(99u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32)).to_equal(-38)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/arch/x86_32_interrupt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering x86_32 interrupt runtime bridge.
- x86_32 interrupt runtime bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a91264686cc1e2b692a00443bf8269801f3d6b2a94707b40c428fa47dbc488f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a91264686cc1e2b692a00443bf8269801f3d6b2a94707b40c428fa47dbc488f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a91264686cc1e2b692a00443bf8269801f3d6b2a94707b40c428fa47dbc488f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/kernel/arch/x86_32_interrupt_spec.spl
mirror: doc/06_spec/unit/os/kernel/arch/x86_32_interrupt_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/arch/x86_32_interrupt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/arch/x86_32_interrupt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/arch/x86_32_interrupt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/arch/x86_32_interrupt_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails cleanly before runtime installation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/x86_32_interrupt_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'installs runtime through the HAL wrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/x86_32_interrupt_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches getpid through a trapped context' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
