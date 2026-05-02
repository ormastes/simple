# SPM Privilege Check Task Mirror Architecture

Feature: FR-SPM-0002.

## Boundary

`syscall_handler` already resolves the caller as a task. Case 110 now passes
that caller task id into the SPM privilege-check handler. The handler remains
inside `src/os/kernel/ipc/syscall.spl` because it owns syscall argument copy-in.

## Flow

1. Copy the id-path bytes from the syscall arguments.
2. Reject empty id paths.
3. Look up the caller's `PrivilegeTokenMirror` through
   `bridge_lookup(caller_task_id)`.
4. Reuse `two_gate_check` to evaluate the copied id path.
5. Return `1` for allow and `0` for deny.
