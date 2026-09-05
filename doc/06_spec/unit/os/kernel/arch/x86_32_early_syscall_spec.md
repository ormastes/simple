# X86 32 Early Syscall Specification

> Tests covering x86_32 freestanding early syscall ABI.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 32 Early Syscall Specification

## Scenarios

### x86_32 freestanding early syscall ABI

#### handles process, brk, reboot, diagnostics, and shell smoke syscalls

- handles process, brk, reboot, diagnostics, and shell smoke syscalls
   - Expected: pid equals `1001`
   - Expected: x86_32_dispatch_installed_syscall_abi(15u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32) equals `1`
   - Expected: x86_32_dispatch_installed_syscall_abi(15u32, 0x30001000u32, 0u32, 0u32, 0u32, 0u32, 0u32) equals `1`
   - Expected: x86_32_dispatch_installed_syscall_abi(16u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32) equals `0`
   - Expected: x86_32_dispatch_installed_syscall_abi(5u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32) equals `2`
   - Expected: x86_32_dispatch_installed_syscall_abi(6u32, pid as u32, 0u32, 0u32, 0u32, 0u32, 0u32) equals `0`
   - Expected: x86_32_dispatch_installed_syscall_abi(13u32, 4u32, 0u32, 0u32, 0u32, 0u32, 0u32) equals `1002`
   - Expected: x86_32_dispatch_installed_syscall_abi(99u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32) equals `-38`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles process, brk, reboot, diagnostics, and shell smoke syscalls")
"""The early ABI returns concrete non-error results without x86_64 helpers."""
x86_32_install_early_syscall_runtime()

val pid = x86_32_dispatch_installed_syscall_abi(2u32, 0x1000u32, 0u32, 0u32, 0u32, 0u32, 0u32)
expect(pid).to_equal(1001)
expect(x86_32_dispatch_installed_syscall_abi(15u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32)).to_equal(1)
expect(x86_32_dispatch_installed_syscall_abi(15u32, 0x30001000u32, 0u32, 0u32, 0u32, 0u32, 0u32)).to_equal(1)
expect(x86_32_dispatch_installed_syscall_abi(16u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32)).to_equal(0)
expect(x86_32_dispatch_installed_syscall_abi(5u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32)).to_equal(2)
expect(x86_32_dispatch_installed_syscall_abi(6u32, pid as u32, 0u32, 0u32, 0u32, 0u32, 0u32)).to_equal(0)
expect(x86_32_dispatch_installed_syscall_abi(13u32, 4u32, 0u32, 0u32, 0u32, 0u32, 0u32)).to_equal(1002)
expect(x86_32_dispatch_installed_syscall_abi(99u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32)).to_equal(-38)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/arch/x86_32_early_syscall_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering x86_32 freestanding early syscall ABI.
- x86_32 freestanding early syscall ABI

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `5c12922fa00b22007d3d1666fbb0b953e07b5bc5090f56e74a620f00fe107156`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5c12922fa00b22007d3d1666fbb0b953e07b5bc5090f56e74a620f00fe107156`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5c12922fa00b22007d3d1666fbb0b953e07b5bc5090f56e74a620f00fe107156`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/os/kernel/arch/x86_32_early_syscall_spec.spl
mirror: doc/06_spec/unit/os/kernel/arch/x86_32_early_syscall_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/arch/x86_32_early_syscall_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/arch/x86_32_early_syscall_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/arch/x86_32_early_syscall_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/arch/x86_32_early_syscall_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles process, brk, reboot, diagnostics, and shell smoke syscalls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
