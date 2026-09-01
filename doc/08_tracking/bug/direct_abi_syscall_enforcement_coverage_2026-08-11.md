# Incomplete direct ABI syscall enforcement coverage

**Status:** Open — blocks `simple_os_enhance` AC-2 and AC-5 whole-surface claim

## Current protected surface

All normal C ABI handlers for process/lifecycle, IPC/notifications, VFS/POSIX
FD composition, time/log/sysinfo, network, device, and G11–G13/scheduler
control now dispatch through `syscall_handler_ipc_state`. The dispatcher
constructs authority from the current scheduler task, applies its immutable
syscall allowlist, and uses the TCB CSpace for every protected capability
decision; the disconnected `IpcManager` ledger is no longer an authorization
source. The
functional `socket()` compatibility allocator is a dispatcher special case,
so its live `NetConnect` check occurs before allocating an FD.

The VFS calls (`open`, `read`, `write`, `close`, `stat`, `mkdir`, `readdir`,
`unlink`, `rename`, `rmdir`, `chdir`, and descriptor-only operations) retain
their existing concrete-path or descriptor checks in `syscall_file`; the
dispatcher supplies the common syscall-filter gate.

Mount and unmount also use the common dispatcher and check `SystemMount` in the
live TCB CSpace before submitting the request to VFS.

The privileged syscall-14 `enter_user_blocking` handoff is also state-dispatched
and requires the live `ProcessSpawn` capability. Global VFS paths remain a
separate isolation issue.

## Required resolution

1. Prove in the target C/assembly syscall table that every trap target resolves
   to a dispatcher bridge.
2. Pass `KernelCallContext` to filesystem, network, device, and process-view
   handlers; remove scalar caller fallback from user-origin paths.
3. Add one adversarial system scenario per class proving an unlisted syscall
   and a missing object capability both fail before side effects.
4. Run the target QEMU syscall-entry path; host interpreter tests alone do not
   prove the C/assembly trap route.
