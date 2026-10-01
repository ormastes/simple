# X86 32 Trap Model Specification

> Tests covering x86_32 trap model.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 32 Trap Model Specification

## Scenarios

### x86_32 trap model

#### marshals int 0x80 registers into syscall args

- marshals int 0x80 registers into syscall args
   - Expected: args.id equals `60`
   - Expected: args.arg0 equals `10`
   - Expected: args.arg1 equals `11`
   - Expected: args.arg2 equals `12`
   - Expected: args.arg3 equals `13`
   - Expected: args.arg4 equals `14`
   - Expected: args.arg5 equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marshals int 0x80 registers into syscall args")
"""eax is syscall id; ebx/ecx/edx/esi/edi/ebp are args 0..5."""
val args = x86_32_syscall_args_from_context(make_context())
expect(args.id).to_equal(60)
expect(args.arg0).to_equal(10)
expect(args.arg1).to_equal(11)
expect(args.arg2).to_equal(12)
expect(args.arg3).to_equal(13)
expect(args.arg4).to_equal(14)
expect(args.arg5).to_equal(15)
```

</details>

#### applies syscall result to eax and advances past int 0x80

- applies syscall result to eax and advances past int 0x80
   - Expected: updated.eax equals `42u32`
   - Expected: updated.eip equals `0x1000u32 + X86_32_INT80_SIZE`
   - Expected: updated.esp equals `0x9000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("applies syscall result to eax and advances past int 0x80")
"""A completed syscall returns through eax and resumes after CD 80."""
val updated = x86_32_apply_syscall_result(make_context(), SyscallResult(value: 42))
expect(updated.eax).to_equal(42u32)
expect(updated.eip).to_equal(0x1000u32 + X86_32_INT80_SIZE)
expect(updated.esp).to_equal(0x9000u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/arch/x86_32_trap_model_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering x86_32 trap model.
- x86_32 trap model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `e3520efab40ec048e348442d747e786359bd0ebf9dc5d7f7efe6157d62bfa50e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e3520efab40ec048e348442d747e786359bd0ebf9dc5d7f7efe6157d62bfa50e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e3520efab40ec048e348442d747e786359bd0ebf9dc5d7f7efe6157d62bfa50e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/os/kernel/arch/x86_32_trap_model_spec.spl
mirror: doc/06_spec/unit/os/kernel/arch/x86_32_trap_model_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/arch/x86_32_trap_model_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/arch/x86_32_trap_model_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/arch/x86_32_trap_model_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/os/kernel/arch/x86_32_trap_model_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marshals int 0x80 registers into syscall args' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/x86_32_trap_model_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'applies syscall result to eax and advances past int 0x80' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
