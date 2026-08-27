# X86 32 Interrupt Specification

> _Hosted coverage for the future i386 int 0x80 runtime bridge._

<!-- sdn-diagram:id=x86_32_interrupt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_32_interrupt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_32_interrupt_spec -> std
x86_32_interrupt_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_32_interrupt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 32 Interrupt Specification

## Scenarios

### x86_32 interrupt runtime bridge
_Hosted coverage for the future i386 int 0x80 runtime bridge._

#### fails cleanly before runtime installation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = x86_32_dispatch_context(syscall_context(4u32))
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap()).to_contain("runtime is not installed")
```

</details>

#### installs runtime through the HAL wrapper

1. intr install runtime
   - Expected: intr.runtime_installed() is true
   - Expected: x86_32_runtime_installed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val intr = X86_32Interrupt()
intr.install_runtime(Scheduler.new(), IpcManager.new(), KernelLog.new(8))
expect(intr.runtime_installed()).to_equal(true)
expect(x86_32_runtime_installed()).to_equal(true)
```

</details>

#### dispatches getpid through a trapped context

1. intr install runtime
   - Expected: result.is_err() is false
   - Expected: updated.eax equals `0u32`
   - Expected: updated.eip equals `0x1002u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. brk reset for test
2. intr install runtime
   - Expected: result.is_err() is false
   - Expected: updated.eax equals `0x30000000u32`
   - Expected: updated.eip equals `0x1002u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. intr install runtime
   - Expected: x86_32_dispatch_installed_syscall_abi(4u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32) equals `0`
   - Expected: x86_32_dispatch_installed_syscall_abi(99u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32) equals `-38`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/os/kernel/arch/x86_32_interrupt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
