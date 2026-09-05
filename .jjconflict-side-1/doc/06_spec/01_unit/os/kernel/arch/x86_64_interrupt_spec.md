# X86 64 Interrupt Specification

> <details>

<!-- sdn-diagram:id=x86_64_interrupt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_64_interrupt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_64_interrupt_spec -> std
x86_64_interrupt_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_64_interrupt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 64 Interrupt Specification

## Scenarios

### x86_64 interrupt runtime bridge

#### reports missing runtime until installed

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(x86_runtime_installed()).to_equal(false)
```

</details>

#### fails cleanly when syscall dispatch runs without runtime

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = x86_dispatch_installed_syscall(SyscallArgs(
    id: 4,
    arg0: 0,
    arg1: 0,
    arg2: 0,
    arg3: 0,
    arg4: 0,
    arg5: 0
))
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap()).to_contain("runtime is not installed")

val entries = x86_read_trap_log(0, 0, 4)
expect(entries.len()).to_equal(0)
```

</details>

#### allows direct runtime installation

1. x86 install runtime
   - Expected: x86_runtime_installed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
x86_install_runtime(Scheduler.new(), IpcManager.new(), KernelLog.new(16))
expect(x86_runtime_installed()).to_equal(true)
```

</details>

#### allows the interrupt HAL to own runtime installation

1. X86Interrupt install runtime
   - Expected: X86Interrupt.runtime_installed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
X86Interrupt.install_runtime(Scheduler.new(), IpcManager.new(), KernelLog.new(8))
expect(X86Interrupt.runtime_installed()).to_equal(true)
```

</details>

#### accepts a precomposed trap runtime bundle

1. X86Interrupt install runtime bundle
   - Expected: X86Interrupt.runtime_installed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = X86TrapRuntime.new(Scheduler.new(), IpcManager.new(), KernelLog.new(8))
X86Interrupt.install_runtime_bundle(runtime)
expect(X86Interrupt.runtime_installed()).to_equal(true)
```

</details>

#### accepts a bootstrap runtime install

1. X86Interrupt install bootstrap runtime
   - Expected: X86Interrupt.runtime_installed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
X86Interrupt.install_bootstrap_runtime(8)
expect(X86Interrupt.runtime_installed()).to_equal(true)
```

</details>

#### dispatches a syscall through installed runtime objects

1. x86 install runtime
   - Expected: result.is_err() is false
   - Expected: result.unwrap().value equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
x86_install_runtime(Scheduler.new(), IpcManager.new(), KernelLog.new(16))

val result = x86_dispatch_installed_syscall(SyscallArgs(
    id: 4,
    arg0: 0,
    arg1: 0,
    arg2: 0,
    arg3: 0,
    arg4: 0,
    arg5: 0
))
expect(result.is_err()).to_equal(false)
expect(result.unwrap().value).to_equal(0)
```

</details>

#### exposes a primitive ABI bridge for C-side callers

1. x86 install runtime
   - Expected: x86_dispatch_installed_syscall_abi(4, 0, 0, 0, 0, 0, 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
x86_install_runtime(Scheduler.new(), IpcManager.new(), KernelLog.new(16))
expect(x86_dispatch_installed_syscall_abi(4, 0, 0, 0, 0, 0, 0)).to_equal(0)
```

</details>

#### preserves scheduler state for direct spawn through the installed bundle

1.  clear synthetic vfs for test
2.  set synthetic vfs file for test
3. var scheduler = Scheduler new
4. X86Interrupt install runtime bundle
   - Expected: found equals `1`
   - Expected: task.is_user is true
   - Expected: task.entry_point equals `0x400000`
5.  clear synthetic vfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_vfs_for_test()
_set_synthetic_vfs_file_for_test("/sys/apps/hello_world", _make_x86_64_exec())

var scheduler = Scheduler.new()
val runtime = X86TrapRuntime.new(scheduler, IpcManager.new(), KernelLog.new(16))
X86Interrupt.install_runtime_bundle(runtime)

val pid = x86_dispatch_installed_syscall_abi(13, 3, 0, 2, 0, 0, 0)
expect(pid).to_be_greater_than(0)

val spawned = scheduler.get_task(TaskId(id: pid as u64))
val found = if spawned == nil: 0 else: 1
expect(found).to_equal(1)
if spawned != nil:
    val task = spawned
    expect(task.is_user).to_equal(true)
    expect(task.entry_point).to_equal(0x400000)

_clear_synthetic_vfs_for_test()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/x86_64_interrupt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86_64 interrupt runtime bridge

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
