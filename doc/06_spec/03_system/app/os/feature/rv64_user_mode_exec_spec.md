# RV64 User Mode Exec Contract

> This pure system spec protects the RV64 user-mode execution contract before deeper runtime integration work: user and kernel contexts must differ in return privilege, user ecalls and external interrupts must classify differently, the syscall ABI must preserve register mapping, and syscall result write-back must advance `sepc` past the ecall.

<!-- sdn-diagram:id=rv64_user_mode_exec_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rv64_user_mode_exec_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rv64_user_mode_exec_spec -> std
rv64_user_mode_exec_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rv64_user_mode_exec_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64 User Mode Exec Contract

This pure system spec protects the RV64 user-mode execution contract before deeper runtime integration work: user and kernel contexts must differ in return privilege, user ecalls and external interrupts must classify differently, the syscall ABI must preserve register mapping, and syscall result write-back must advance `sepc` past the ecall.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/os/feature/rv64_user_mode_exec_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This pure system spec protects the RV64 user-mode execution contract before
deeper runtime integration work: user and kernel contexts must differ in return
privilege, user ecalls and external interrupts must classify differently, the
syscall ABI must preserve register mapping, and syscall result write-back must
advance `sepc` past the ecall.

## Scenarios

### rv64_user_mode_exec feature spec

#### keeps kernel and user initial return privilege distinct

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kernel_ctx = create_rv64_kernel_context(0x80200000, 0x80400000, 0)
val user_ctx = create_rv64_user_context(0x400000, 0x410000, 0)
expect((kernel_ctx.sstatus & RV64_SSTATUS_SPP) != 0).to_equal(true)
expect((user_ctx.sstatus & RV64_SSTATUS_SPP) != 0).to_equal(false)
```

</details>

#### classifies user ecall as the supported runtime syscall path

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scause = RV64_CAUSE_ECALL_FROM_U
val kind = classify_rv64_trap(scause)
match kind:
    case Rv64TrapKind.UserEcall:
        expect((scause & RV64_CAUSE_INTERRUPT_BIT) != 0).to_equal(false)
        expect(scause == RV64_CAUSE_ECALL_FROM_U).to_equal(true)
    case _:
        expect(kind).to_equal(Rv64TrapKind.UserEcall)
```

</details>

#### keeps external interrupts separate from user ecall handling

<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scause = RV64_CAUSE_INTERRUPT_BIT + RV64_CAUSE_S_EXTERNAL_INTERRUPT
val kind = classify_rv64_trap(scause)
match kind:
    case Rv64TrapKind.ExternalInterrupt:
        expect((scause & RV64_CAUSE_INTERRUPT_BIT) != 0).to_equal(true)
        expect((scause & 0x7FFFFFFFFFFFFFFF) == RV64_CAUSE_S_EXTERNAL_INTERRUPT).to_equal(true)
    case _:
        expect(kind).to_equal(Rv64TrapKind.ExternalInterrupt)
```

</details>

#### maps rv64 syscall registers to the stable syscall ABI

<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = Riscv64Context(
    ra: 0, sp: 0, gp: 0, tp: 0,
    t0: 0, t1: 0, t2: 0,
    s0: 0, s1: 0,
    a0: 1, a1: 2, a2: 3, a3: 4, a4: 5, a5: 6, a6: 0, a7: 60,
    s2: 0, s3: 0, s4: 0, s5: 0, s6: 0, s7: 0, s8: 0, s9: 0, s10: 0, s11: 0,
    t3: 0, t4: 0, t5: 0, t6: 0,
    sepc: 0x1000,
    sstatus: 0,
    scause: RV64_CAUSE_ECALL_FROM_U
)
val args = rv64_syscall_args_from_context(ctx)
expect(args.id).to_equal(60)
expect(args.arg0).to_equal(1)
expect(args.arg5).to_equal(6)
```

</details>

#### writes syscall result to a0 and advances sepc past ecall

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = create_rv64_user_context(0x400000, 0x410000, 0)
val updated = rv64_apply_syscall_result(ctx, SyscallResult(value: 7))
expect(updated.a0).to_equal(7)
expect(updated.sepc).to_equal(0x400004)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
