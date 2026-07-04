# X86 32 Context Specification

> _Pure register-frame construction for the x86_32 HAL context path._

<!-- sdn-diagram:id=x86_32_context_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_32_context_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_32_context_spec -> std
x86_32_context_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_32_context_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 32 Context Specification

## Scenarios

### x86_32 context construction
_Pure register-frame construction for the x86_32 HAL context path._

#### creates a kernel context with aligned stack and ring-0 selectors

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. ops switch
   - Expected: to_ctx.eip equals `0x2000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val from_ctx = X86_32ContextSwitch.create(0x1000u32, 0x9000u32, false)
val to_ctx = X86_32ContextSwitch.create(0x2000u32, 0xA000u32, false)
val ops = X86_32ContextSwitch()
ops.switch(from_ctx, to_ctx)
expect(to_ctx.eip).to_equal(0x2000u32)
```

</details>

#### skips FPU hooks until a state buffer is assigned

1. ops save fpu
2. ops restore fpu
   - Expected: ctx.fpu_state equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/os/kernel/arch/x86_32_context_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
