# Riscv64 Interrupt Specification

> <details>

<!-- sdn-diagram:id=riscv64_interrupt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv64_interrupt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv64_interrupt_spec -> std
riscv64_interrupt_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv64_interrupt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv64 Interrupt Specification

## Scenarios

### rv64 interrupt runtime bridge

#### reports missing runtime until installed

<details>
<summary>Executable SPipe</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(rv64_runtime_installed()).to_equal(false)
```

</details>

#### dispatches a user ecall through installed runtime objects

1. rv64 install trap runtime
   - Expected: rv64_runtime_installed() is true

2. var ctx = create rv64 user context
   - Expected: result.is_err() is false
   - Expected: updated.a0 equals `0`
   - Expected: updated.sepc equals `0x400004`


<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rv64_install_trap_runtime(Scheduler.new(), IpcManager.new(), KernelLog.new(16))
expect(rv64_runtime_installed()).to_equal(true)

var ctx = create_rv64_user_context(0x400000, 0x410000, 0)
ctx.a7 = 4      # GetPid
ctx.scause = RV64_CAUSE_ECALL_FROM_U

val result = rv64_dispatch_installed_trap(ctx)
expect(result.is_err()).to_equal(false)

val updated = result.unwrap()
expect(updated.a0).to_equal(0)
expect(updated.sepc).to_equal(0x400004)
```

</details>

#### rejects unsupported supervisor ecalls

1. rv64 install trap runtime

2. var ctx = create rv64 user context
   - Expected: result.is_err() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rv64_install_trap_runtime(Scheduler.new(), IpcManager.new(), KernelLog.new(16))

var ctx = create_rv64_user_context(0x400000, 0x410000, 0)
ctx.a7 = 4
ctx.scause = 9

val result = rv64_dispatch_installed_trap(ctx)
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap()).to_contain("unsupported RV64 supervisor ecall")
```

</details>

#### allows the interrupt HAL to own runtime installation

1. Rv64Interrupt install runtime
   - Expected: Rv64Interrupt.runtime_installed() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Rv64Interrupt.install_runtime(Scheduler.new(), IpcManager.new(), KernelLog.new(8))
expect(Rv64Interrupt.runtime_installed()).to_equal(true)
```

</details>

#### accepts a precomposed trap runtime bundle

1. Rv64Interrupt install runtime bundle
   - Expected: Rv64Interrupt.runtime_installed() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = Rv64TrapRuntime.new(Scheduler.new(), IpcManager.new(), KernelLog.new(8))
Rv64Interrupt.install_runtime_bundle(runtime)
expect(Rv64Interrupt.runtime_installed()).to_equal(true)
```

</details>

#### accepts a bootstrap trap runtime install

1. Rv64Interrupt install bootstrap runtime
   - Expected: Rv64Interrupt.runtime_installed() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
Rv64Interrupt.install_bootstrap_runtime(8)
expect(Rv64Interrupt.runtime_installed()).to_equal(true)
```

</details>

#### records trap failures in the installed kernel log

1. rv64 install trap runtime

2. var ctx = create rv64 user context
   - Expected: result.is_err() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rv64_install_trap_runtime(Scheduler.new(), IpcManager.new(), KernelLog.new(8))

var ctx = create_rv64_user_context(0x400000, 0x410000, 0)
ctx.a7 = 4
ctx.scause = 9

val result = rv64_dispatch_installed_trap(ctx)
expect(result.is_err()).to_equal(true)

val entries = rv64_read_trap_log(0, 0, 4)
expect(entries.len()).to_be_greater_than(0)
expect(entries[entries.len() - 1].message).to_contain("unsupported RV64 supervisor ecall")
```

</details>

#### updates a trap frame through the installed dispatch bridge

1. rv64 install trap runtime

2. var ctx = create rv64 user context
   - Expected: result.is_ok() is true
   - Expected: updated.a0 equals `0`
   - Expected: updated.sepc equals `0x400004`


<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rv64_install_trap_runtime(Scheduler.new(), IpcManager.new(), KernelLog.new(8))

var ctx = create_rv64_user_context(0x400000, 0x410000, 0)
ctx.a7 = 4
ctx.scause = RV64_CAUSE_ECALL_FROM_U

val result = rv64_dispatch_installed_trap(ctx)
expect(result.is_ok()).to_equal(true)
val updated = result.unwrap()
expect(updated.a0).to_equal(0)
expect(updated.sepc).to_equal(0x400004)
```

</details>

#### rejects a null trap frame pointer

1. rv64 install trap runtime
   - Expected: rc equals `-1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
rv64_install_trap_runtime(Scheduler.new(), IpcManager.new(), KernelLog.new(8))

val rc = rv64_dispatch_trap_frame_ptr(0)
expect(rc).to_equal(-1)

val entries = rv64_read_trap_log(0, 0, 4)
expect(entries.len()).to_be_greater_than(0)
expect(entries[entries.len() - 1].message).to_contain("trap frame pointer is null")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/riscv64_interrupt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- rv64 interrupt runtime bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
