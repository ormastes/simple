# Execve Syscall — Kernel Developer Guide

## Overview

The `execve` syscall (number **59**) replaces the current process image with a
new executable while preserving the calling task's PID, parent linkage, and
non-close-on-exec file descriptors. This is the SimpleOS equivalent of the
POSIX `execve(path, argv, envp)` interface.

## Syscall ABI

| Register | Field | Description |
|----------|-------|-------------|
| arg0 | path_ptr | Userspace pointer to executable path bytes |
| arg1 | path_len | Length of path in bytes (max 256) |
| arg2 | argv_ptr | Userspace `char**` vector for arguments (NULL-terminated, or 0 to skip) |
| arg3 | envp_ptr | Userspace `char**` vector for environment (NULL-terminated, or 0 to skip) |

**Returns:** 0 on success. On error, a negative errno:

| Code | Value | Meaning |
|------|-------|---------|
| EINVAL | -22 | Null path pointer or zero length |
| ENAMETOOLONG | -36 | Path exceeds MAX_BINARY_PATH_LEN (256) |
| EFAULT | -14 | Cannot copy path bytes from userspace |
| ENOENT | -2 | Executable not found by resolver |
| ENOEXEC | -8 | ELF parsing or image building failed |

## Execution Flow

```
_handle_exec(args, scheduler)
    |
    +-- 1. Validate path pointer and length
    |       - arg0 != 0, arg1 != 0, arg1 <= MAX_BINARY_PATH_LEN
    |
    +-- 2. Copy path bytes from userspace
    |       - _copy_user_bytes(arg0, arg1)
    |
    +-- 3. Copy argv/envp vectors from userspace
    |       - vmm_copyin_string_vector() for each
    |       - Enforces MAX_EXEC_ARG_COUNT (64), MAX_EXEC_ENV_COUNT (128)
    |       - Per-string limit: MAX_EXEC_STRING_LEN (4096)
    |       - Total byte limit: MAX_EXEC_TOTAL_STRING_BYTES (32768)
    |
    +-- 4. Resolve executable bytes
    |       - resolve_executable_bytes_from_path_bytes(path, arch)
    |       - Checks VFS, boot-packaged binaries, app registry
    |
    +-- 5. Build new process image (BEFORE teardown)
    |       - build_user_process_image(path, bytes, arch, argv, envp)
    |       - Parses ELF, creates UserProcessImage with segments + stack
    |       - If this fails, the original process survives (atomicity)
    |
    +-- 6. Replace task image via scheduler
    |       - scheduler.exec_image(current_task, image)
    |         a. Create new AddressSpace
    |         b. Map new image segments + stack into new address space
    |         c. Release old address space (_release_task_address_space)
    |         d. Update TCB: entry_point, context, user_context,
    |            address_space, user_stack, isolation, exit_code
    |         e. Set user_context RIP = new entry, RSP = new stack
    |         f. Re-enqueue task if it was ready
    |
    +-- 7. Close CLOEXEC file descriptors
    |       - _close_cloexec_fds_with_backends()
    |
    +-- 8. Register new VMSpace
            - vmm_new_process_space() + register_task_vmspace()
```

## Atomicity Guarantees

The implementation follows a **build-before-teardown** strategy:

1. The new `UserProcessImage` is fully constructed (ELF parsed, segments
   extracted, SysV stack frame built) **before** the old address space is
   touched.
2. Only after `build_user_process_image()` succeeds does
   `scheduler.exec_image()` call `_release_task_address_space()` to destroy
   the old mappings.
3. If ELF parsing or image construction fails at step 5, `_handle_exec`
   returns an error code and the calling process continues running its
   original image unmodified.
4. If address-space mapping fails inside `exec_image`, the new address space
   is destroyed and the old task is re-enqueued in its original state.

## Trap-Frame Resume Behavior

After `exec_image()` succeeds, the TCB's `user_context` is overwritten with:

- **RIP** = mapped entry point (from ELF e_entry, potentially relocated by
  direct-load mapper)
- **RSP** = initial stack pointer (16-byte aligned, below the SysV
  argv/envp/auxv frame)
- **All GPRs** = zeroed (clean register state for the new process)

The next context switch to this task will restore these registers from the
TCB's `user_context`, causing execution to begin at the new entry point
rather than returning to the old syscall call site. This is the key
difference from other syscalls: exec does not return to the caller on
success.

## Key Differences from SpawnBinary (syscall 13)

| Aspect | SpawnBinary (13) | Exec (59) |
|--------|------------------|-----------|
| PID | New PID allocated | Same PID preserved |
| Address space | New address space, new task | Old space torn down, new space mapped into same TCB |
| File descriptors | Independent FD table | CLOEXEC FDs closed, others preserved |
| Parent | Current task becomes parent | Parent linkage unchanged |
| Capabilities | Fresh CapabilitySet | Capability generation incremented |
| Return value | Child PID (positive) | 0 on success |

## Source Files

| File | Function |
|------|----------|
| `src/os/kernel/ipc/syscall.spl` | `_handle_exec()` — syscall entry point |
| `src/os/kernel/scheduler/scheduler.spl` | `exec_image()` — TCB + address space replacement |
| `src/os/kernel/scheduler/scheduler.spl` | `_release_task_address_space()` — old AS cleanup |
| `src/os/kernel/memory/vmm.spl` | `vmm_teardown_user_space()` — VMA + page teardown |
| `src/os/kernel/loader/process_image.spl` | `build_user_process_image()` — ELF to image |
| `src/os/kernel/loader/executable_source.spl` | `resolve_executable_bytes()` — path resolution |
| `test/unit/os/kernel/ipc/execve_spec.spl` | BDD specification |
