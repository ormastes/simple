# X86 32 Context Specification

> Tests covering x86_32 context construction.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 32 Context Specification

## Scenarios

### x86_32 context construction

#### creates a kernel context with aligned stack and ring-0 selectors

- creates a kernel context with aligned stack and ring-0 selectors
   - Expected: ctx.eip equals `0x100123u32`
   - Expected: ctx.esp equals `0x80000ff0u32`
   - Expected: ctx.ebp equals `0x80000ff0u32`
   - Expected: ctx.cs equals `GDT_KERNEL_CODE as u32`
   - Expected: ctx.ss equals `GDT_KERNEL_DATA as u32`
   - Expected: ctx.ds equals `GDT_KERNEL_DATA as u32`
   - Expected: ctx.es equals `GDT_KERNEL_DATA as u32`
   - Expected: ctx.eflags equals `0x202u32`
   - Expected: ctx.fpu_state equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a kernel context with aligned stack and ring-0 selectors")
"""Kernel contexts should start at the requested EIP with ring-0 segments."""
val ctx = X86_32ContextSwitch.create(0x100123u32, 0x80000fffu32, false)
expect(ctx.eip).to_equal(0x100123u32)
expect(ctx.esp).to_equal(0x80000ff0u32)
expect(ctx.ebp).to_equal(0x80000ff0u32)
expect(ctx.cs).to_equal(GDT_KERNEL_CODE as u32)
expect(ctx.ss).to_equal(GDT_KERNEL_DATA as u32)
expect(ctx.ds).to_equal(GDT_KERNEL_DATA as u32)
expect(ctx.es).to_equal(GDT_KERNEL_DATA as u32)
expect(ctx.eflags).to_equal(0x202u32)
expect(ctx.fpu_state).to_equal(0u32)
```

</details>

#### creates a user context with ring-3 selectors

- creates a user context with ring-3 selectors
   - Expected: ctx.eip equals `0x00401000u32`
   - Expected: ctx.esp equals `0xBFFFFFE0u32`
   - Expected: ctx.cs equals `(GDT_USER_CODE as u32) | 3u32`
   - Expected: ctx.ss equals `(GDT_USER_DATA as u32) | 3u32`
   - Expected: ctx.ds equals `(GDT_USER_DATA as u32) | 3u32`
   - Expected: ctx.es equals `(GDT_USER_DATA as u32) | 3u32`
   - Expected: ctx.eflags equals `0x202u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates a user context with ring-3 selectors")
"""User contexts should use RPL=3 code/data selectors and aligned ESP."""
val ctx = X86_32ContextSwitch.create(0x00401000u32, 0xBFFFFFEFu32, true)
expect(ctx.eip).to_equal(0x00401000u32)
expect(ctx.esp).to_equal(0xBFFFFFE0u32)
expect(ctx.cs).to_equal((GDT_USER_CODE as u32) | 3u32)
expect(ctx.ss).to_equal((GDT_USER_DATA as u32) | 3u32)
expect(ctx.ds).to_equal((GDT_USER_DATA as u32) | 3u32)
expect(ctx.es).to_equal((GDT_USER_DATA as u32) | 3u32)
expect(ctx.eflags).to_equal(0x202u32)
```

</details>

#### routes context switch through the runtime hook

- routes context switch through the runtime hook
   - Expected: to_ctx.eip equals `0x2000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes context switch through the runtime hook")
"""The hosted test runtime should tolerate the x86_32 switch hook call."""
val from_ctx = X86_32ContextSwitch.create(0x1000u32, 0x9000u32, false)
val to_ctx = X86_32ContextSwitch.create(0x2000u32, 0xA000u32, false)
val ops = X86_32ContextSwitch()
ops.switch(from_ctx, to_ctx)
expect(to_ctx.eip).to_equal(0x2000u32)
```

</details>

#### skips FPU hooks until a state buffer is assigned

- skips FPU hooks until a state buffer is assigned
   - Expected: ctx.fpu_state equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("skips FPU hooks until a state buffer is assigned")
"""Zero fpu_state is a valid lazy-FPU state and should be a no-op."""
val ctx = X86_32ContextSwitch.create(0x1000u32, 0x9000u32, false)
val ops = X86_32ContextSwitch()
ops.save_fpu(ctx)
ops.restore_fpu(ctx)
expect(ctx.fpu_state).to_equal(0u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/arch/x86_32_context_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering x86_32 context construction.
- x86_32 context construction

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

- Canonical SPipe generation for source `ddca4cc5b17a41276bdc80e17eea97642c64a2035dc261bab4ddc4e4df065ea8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ddca4cc5b17a41276bdc80e17eea97642c64a2035dc261bab4ddc4e4df065ea8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ddca4cc5b17a41276bdc80e17eea97642c64a2035dc261bab4ddc4e4df065ea8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/arch/x86_32_context_spec.spl
mirror: doc/06_spec/unit/os/kernel/arch/x86_32_context_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/arch/x86_32_context_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/arch/x86_32_context_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/arch/x86_32_context_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a kernel context with aligned stack and ring-0 selectors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/x86_32_context_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a user context with ring-3 selectors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/x86_32_context_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes context switch through the runtime hook' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
