# Kernel Mvp Specification

> <details>

<!-- sdn-diagram:id=kernel_mvp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=kernel_mvp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

kernel_mvp_spec -> std
kernel_mvp_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=kernel_mvp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kernel Mvp Specification

## Scenarios

### x86_64_ring3_smoke

#### creates a ring-3 context with the user selectors and aligned stack

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ctx = X86ContextSwitch.create(0x401000, X86_64_USER_STACK_TOP, true)
expect(ctx.cs).to_equal((GDT_USER_CS as u64) | 3)
expect(ctx.ss).to_equal((GDT_USER_DS as u64) | 3)
expect(ctx.rsp % 16).to_equal(0)
expect(ctx.rflags).to_equal(0x202)
```

</details>

#### builds an x86_64 user image with the stable stack top

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = build_user_process_image("/usr/bin/x86_exec_probe", _make_x86_64_exec(), Architecture.X86_64)
expect(image.is_ok()).to_equal(true)
val built = image.unwrap()
expect(built.entry).to_equal(0x400000)
expect(built.stack_top).to_equal(X86_64_USER_STACK_TOP)
expect(built.argv[0]).to_equal("/usr/bin/x86_exec_probe")
```

</details>

### x86_64_fat32_exec

#### resolves filesystem-backed x86_64 bytes and builds a process image

1.  clear synthetic vfs for test
2.  set synthetic vfs file for test
   - Expected: bytes.is_ok() is true
   - Expected: image.is_ok() is true
   - Expected: built.binary_path equals `/sys/apps/hello_world`
   - Expected: built.entry equals `0x400000`
   - Expected: built.stack_top equals `X86_64_USER_STACK_TOP`
3.  clear synthetic vfs for test


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
_clear_synthetic_vfs_for_test()
_set_synthetic_vfs_file_for_test("/sys/apps/hello_world", _make_x86_64_exec())
val bytes = resolve_executable_bytes("/sys/apps/hello_world", Architecture.X86_64)
expect(bytes.is_ok()).to_equal(true)

val image = build_user_process_image("/sys/apps/hello_world", bytes.unwrap(), Architecture.X86_64)
expect(image.is_ok()).to_equal(true)
val built = image.unwrap()
expect(built.binary_path).to_equal("/sys/apps/hello_world")
expect(built.entry).to_equal(0x400000)
expect(built.stack_top).to_equal(X86_64_USER_STACK_TOP)
_clear_synthetic_vfs_for_test()
```

</details>

### x86_64_shell_smoke

#### advertises dmesg in the shell help output

1. shell execute
   - Expected: shell.last_exit_code equals `0`
   - Expected: _contains_line(shell.output_lines, "dmesg [N]") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val shell = ShellApp.new()
shell.output_lines = []
shell.execute("help")
expect(shell.last_exit_code).to_equal(0)
expect(_contains_line(shell.output_lines, "dmesg [N]")).to_equal(true)
```

</details>

### x86_64_fault_smoke

#### rejects ring-3 entry when no user task exists

1. X86Interrupt install bootstrap runtime
   - Expected: x86_dispatch_installed_syscall_abi(14, 0, 0, 0, 0, 0, 0) equals `-22`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
X86Interrupt.install_bootstrap_runtime(8)
expect(x86_dispatch_installed_syscall_abi(14, 0, 0, 0, 0, 0, 0)).to_equal(-22)
```

</details>

#### returns ENOSYS for an unknown installed syscall id

1. X86Interrupt install runtime bundle
   - Expected: result.is_err() is false
   - Expected: result.unwrap().value equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime = X86TrapRuntime.new(Scheduler.new(), IpcManager.new(), KernelLog.new(8))
X86Interrupt.install_runtime_bundle(runtime)
val result = x86_dispatch_installed_syscall(SyscallArgs(
    id: 999,
    arg0: 0,
    arg1: 0,
    arg2: 0,
    arg3: 0,
    arg4: 0,
    arg5: 0
))
expect(result.is_err()).to_equal(false)
expect(result.unwrap().value).to_equal(-1)
```

</details>

### kernel_log_and_dmesg_exposure

#### keeps ordered kernel log entries readable for dmesg-style consumers

1. log write
2. log write
   - Expected: entries.len() equals `2`
   - Expected: entries[0].message equals `boot: service init`
   - Expected: entries[1].message equals `boot: shell ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = KernelLog.new(4)
log.write(3, 1, 101, "boot: service init")
log.write(6, 1, 101, "boot: shell ready")
val entries = log.read(0, 0, 4)
expect(entries.len()).to_equal(2)
expect(entries[0].message).to_equal("boot: service init")
expect(entries[1].message).to_equal("boot: shell ready")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/os/feature/kernel_mvp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86_64_ring3_smoke
- x86_64_fat32_exec
- x86_64_shell_smoke
- x86_64_fault_smoke
- kernel_log_and_dmesg_exposure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
