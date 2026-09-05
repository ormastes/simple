# Riscv64 Trap Model Specification

> <details>

<!-- sdn-diagram:id=riscv64_trap_model_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv64_trap_model_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv64_trap_model_spec -> std
riscv64_trap_model_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv64_trap_model_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv64 Trap Model Specification

## Scenarios

### rv64 trap model

#### builds kernel contexts that return to supervisor mode

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = create_rv64_kernel_context(0x80200000, 0x80400000, 7)
expect(rv64_initial_kernel_sstatus() & RV64_SSTATUS_SPIE).to_equal(RV64_SSTATUS_SPIE)
expect(rv64_initial_kernel_sstatus() & RV64_SSTATUS_SPP).to_equal(RV64_SSTATUS_SPP)
expect(ctx.sepc).to_equal(0x80200000)
expect(ctx.sp).to_equal(0x80400000)
expect(ctx.a0).to_equal(7)
expect(ctx.sstatus & RV64_SSTATUS_SPP).to_equal(RV64_SSTATUS_SPP)
```

</details>

#### builds user contexts that return to user mode

<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = create_rv64_user_context(0x400000, 0x410000, 11)
expect(rv64_initial_user_sstatus() & RV64_SSTATUS_SPIE).to_equal(RV64_SSTATUS_SPIE)
expect(rv64_initial_user_sstatus() & RV64_SSTATUS_SPP).to_equal(0)
expect(ctx.sepc).to_equal(0x400000)
expect(ctx.sp).to_equal(0x410000)
expect(ctx.a0).to_equal(0)
expect(ctx.sstatus & RV64_SSTATUS_SPP).to_equal(0)
```

</details>

#### classifies user ecalls

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = classify_rv64_trap(RV64_CAUSE_ECALL_FROM_U)
expect(kind).to_equal(Rv64TrapKind.UserEcall)
```

</details>

#### classifies supervisor timer interrupts

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = classify_rv64_trap(RV64_CAUSE_INTERRUPT_BIT | RV64_CAUSE_S_TIMER_INTERRUPT)
expect(kind).to_equal(Rv64TrapKind.TimerInterrupt)
```

</details>

#### marshals syscall registers from rv64 user context

<details>
<summary>Executable SPipe</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = Riscv64Context(
    ra: 0, sp: 0, gp: 0, tp: 0,
    t0: 0, t1: 0, t2: 0,
    s0: 0, s1: 0,
    a0: 10, a1: 11, a2: 12, a3: 13, a4: 14, a5: 15, a6: 0, a7: 60,
    s2: 0, s3: 0, s4: 0, s5: 0, s6: 0, s7: 0, s8: 0, s9: 0, s10: 0, s11: 0,
    t3: 0, t4: 0, t5: 0, t6: 0,
    sepc: 0x1000,
    sstatus: 0,
    scause: 0
)
val args = rv64_syscall_args_from_context(ctx)
expect(args.id).to_equal(60)
expect(args.arg0).to_equal(10)
expect(args.arg1).to_equal(11)
expect(args.arg2).to_equal(12)
expect(args.arg3).to_equal(13)
expect(args.arg4).to_equal(14)
expect(args.arg5).to_equal(15)
```

</details>

#### applies syscall results back into rv64 user context

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = create_rv64_user_context(0x400000, 0x410000, 1)
val updated = rv64_apply_syscall_result(ctx, SyscallResult(value: 42))
expect(updated.a0).to_equal(42)
expect(updated.sepc).to_equal(0x400004)
expect(updated.sp).to_equal(0x410000)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/riscv64_trap_model_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- rv64 trap model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
