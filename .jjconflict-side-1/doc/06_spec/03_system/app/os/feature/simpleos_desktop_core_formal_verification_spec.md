# SimpleOS Desktop Core Formal Verification Contract

> This pure system spec covers the bounded desktop-core verification surface: RISC-V user/kernel context separation, trap classification, syscall argument marshalling, desktop app-switcher selection, and crash-domain policy. Unexpected enum branches assert the expected enum/domain value directly so failures report which contract value drifted.

<!-- sdn-diagram:id=simpleos_desktop_core_formal_verification_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_desktop_core_formal_verification_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_desktop_core_formal_verification_spec -> std
simpleos_desktop_core_formal_verification_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_desktop_core_formal_verification_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Desktop Core Formal Verification Contract

This pure system spec covers the bounded desktop-core verification surface: RISC-V user/kernel context separation, trap classification, syscall argument marshalling, desktop app-switcher selection, and crash-domain policy. Unexpected enum branches assert the expected enum/domain value directly so failures report which contract value drifted.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/os/feature/simpleos_desktop_core_formal_verification_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This pure system spec covers the bounded desktop-core verification surface:
RISC-V user/kernel context separation, trap classification, syscall argument
marshalling, desktop app-switcher selection, and crash-domain policy. Unexpected
enum branches assert the expected enum/domain value directly so failures report
which contract value drifted.

## Scenarios

### simpleos_desktop_core_formal_verification feature spec

#### REQ-SODCFV-002 keeps kernel and user privilege return state distinct

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

#### REQ-SODCFV-002 preserves user ecall and external interrupt as different kernel-core paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val irq_cause = RV64_CAUSE_INTERRUPT_BIT + RV64_CAUSE_S_EXTERNAL_INTERRUPT
val syscall_kind = classify_rv64_trap(RV64_CAUSE_ECALL_FROM_U)
val irq_kind = classify_rv64_trap(irq_cause)
match syscall_kind:
    case Rv64TrapKind.UserEcall:
        expect(RV64_CAUSE_ECALL_FROM_U).to_equal(8)
        expect((RV64_CAUSE_ECALL_FROM_U & RV64_CAUSE_INTERRUPT_BIT) != 0).to_equal(false)
    case _:
        expect(syscall_kind).to_equal(Rv64TrapKind.UserEcall)
match irq_kind:
    case Rv64TrapKind.ExternalInterrupt:
        expect((irq_cause & RV64_CAUSE_INTERRUPT_BIT) != 0).to_equal(true)
        expect(irq_cause & 0x7FFFFFFFFFFFFFFF).to_equal(RV64_CAUSE_S_EXTERNAL_INTERRUPT)
    case _:
        expect(irq_kind).to_equal(Rv64TrapKind.ExternalInterrupt)
```

</details>

#### REQ-SODCFV-002 keeps syscall register marshalling stable

<details>
<summary>Executable SPipe</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = Riscv64Context(
    ra: 0, sp: 0, gp: 0, tp: 0,
    t0: 0, t1: 0, t2: 0,
    s0: 0, s1: 0,
    a0: 11, a1: 22, a2: 33, a3: 44, a4: 55, a5: 66, a6: 0, a7: 77,
    s2: 0, s3: 0, s4: 0, s5: 0, s6: 0, s7: 0, s8: 0, s9: 0, s10: 0, s11: 0,
    t3: 0, t4: 0, t5: 0, t6: 0,
    sepc: 0x1000,
    sstatus: 0,
    scause: RV64_CAUSE_ECALL_FROM_U
)
val args = rv64_syscall_args_from_context(ctx)
expect(args.id).to_equal(77)
expect(args.arg0).to_equal(11)
expect(args.arg5).to_equal(66)
```

</details>

#### REQ-SODCFV-003 keeps desktop selection unique and updates it after close

1. var switcher = AppSwitcher create

2. [WindowId
   - Expected: switcher.is_visible() is true
   - Expected: switcher.get_selected_window_id()?.value equals `10`

3. switcher select next
   - Expected: switcher.get_selected_window_id()?.value equals `20`
   - Expected: closed?.value equals `20`
   - Expected: switcher.get_selected_window_id()?.value equals `10`


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var switcher = AppSwitcher.create(Px(value: 1280), Px(value: 720))
switcher.show(
    [WindowId(value: 10), WindowId(value: 20)],
    ["Terminal", "Browser"]
)
expect(switcher.is_visible()).to_equal(true)
expect(switcher.get_selected_window_id()?.value).to_equal(10)
switcher.select_next()
expect(switcher.get_selected_window_id()?.value).to_equal(20)
val closed = switcher.close_selected()
expect(closed?.value).to_equal(20)
expect(switcher.get_selected_window_id()?.value).to_equal(10)
```

</details>

#### REQ-SODCFV-003 and NFR-SODCFV-008 keep user apps and kernel components in different crash domains

<details>
<summary>Executable SPipe</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val user_domain = default_fault_domain(AppClass.UserApp)
val kernel_domain = default_fault_domain(AppClass.KernelComponent)
match user_domain:
    case AppFaultDomain.Process:
        val user_policy = default_supervisor_policy(AppClass.UserApp)
        expect(user_policy.max_restarts).to_equal(1)
        expect(user_policy.quarantine_on_limit).to_equal(true)
    case _:
        expect(user_domain).to_equal(AppFaultDomain.Process)
match kernel_domain:
    case AppFaultDomain.KernelResident:
        val kernel_policy = default_supervisor_policy(AppClass.KernelComponent)
        expect(kernel_policy.max_restarts).to_equal(0)
        expect(kernel_policy.quarantine_on_limit).to_equal(false)
    case _:
        expect(kernel_domain).to_equal(AppFaultDomain.KernelResident)
```

</details>

#### REQ-SODCFV-003 keeps restart policy stricter for user apps than for kernel components

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val user_policy = default_supervisor_policy(AppClass.UserApp)
val kernel_policy = default_supervisor_policy(AppClass.KernelComponent)
expect(user_policy.max_restarts).to_equal(1)
expect(kernel_policy.max_restarts).to_equal(0)
expect(user_policy.quarantine_on_limit).to_equal(true)
expect(kernel_policy.quarantine_on_limit).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
