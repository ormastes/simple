# Syscall Entry Specification

> Tests covering kernel.arch.x86_64 SYSCALL trampoline wiring.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Syscall Entry Specification

## Scenarios

### kernel.arch.x86_64 SYSCALL trampoline wiring

#### exposes the trampoline address helper

- exposes the trampoline address helper
   - Expected: a equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exposes the trampoline address helper")
"""`kernel_syscall_entry_addr` must be importable from cpu.spl.
The function simply wraps the C-side `get_kernel_syscall_entry_addr`
so the Simple side can fetch the trampoline address for the
future wrmsr flip without dealing with raw symbol coercion."""
# Call it twice — the contract is "callable without error AND
# deterministic"; link-time presence is verified at kernel build.
val a: u64 = kernel_syscall_entry_addr()
val b: u64 = kernel_syscall_entry_addr()
expect(a).to_equal(b)
```

</details>

#### install_syscall_entry is idempotent

- install_syscall_entry is idempotent
   - Expected: syscall_entry_installed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("install_syscall_entry is idempotent")
"""The installer is called from both os_main and
desktop_e2e_main via arch_x86_64_early_init. It must tolerate
repeat invocations without flipping state back or erroring."""
install_syscall_entry()
install_syscall_entry()
install_syscall_entry()
expect(syscall_entry_installed()).to_equal(true)
```

</details>

#### documents EFER_SCE as bit 0

- documents EFER_SCE as bit 0
   - Expected: EFER_SCE equals `0x1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents EFER_SCE as bit 0")
"""EFER bit 0 enables the SYSCALL/SYSRET instructions. The
planned wrmsr flip will set this bit as the first step, so
lock the numeric value into a spec to guard against typos."""
expect(EFER_SCE).to_equal(0x1)
```

</details>

#### documents SYSCALL_FMASK_IF as RFLAGS bit 9

- documents SYSCALL_FMASK_IF as RFLAGS bit 9
   - Expected: SYSCALL_FMASK_IF equals `0x200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documents SYSCALL_FMASK_IF as RFLAGS bit 9")
"""MSR_SFMASK is programmed to clear IF (RFLAGS bit 9 = 0x200)
on SYSCALL entry so the kernel runs with interrupts disabled
until it is ready to re-enable them. Lock the numeric value."""
expect(SYSCALL_FMASK_IF).to_equal(0x200)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/arch/syscall_entry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering kernel.arch.x86_64 SYSCALL trampoline wiring.
- kernel.arch.x86_64 SYSCALL trampoline wiring

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `353859b50f7e61f495cc27eaa919f66a8a2d7d25d7d40a4c41f15976e3b3de1e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `353859b50f7e61f495cc27eaa919f66a8a2d7d25d7d40a4c41f15976e3b3de1e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `353859b50f7e61f495cc27eaa919f66a8a2d7d25d7d40a4c41f15976e3b3de1e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/arch/syscall_entry_spec.spl
mirror: doc/06_spec/unit/os/kernel/arch/syscall_entry_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/arch/syscall_entry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/arch/syscall_entry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/arch/syscall_entry_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exposes the trampoline address helper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/syscall_entry_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'install_syscall_entry is idempotent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/syscall_entry_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents EFER_SCE as bit 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
