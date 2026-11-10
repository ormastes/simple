# Incomplete direct ABI syscall enforcement coverage
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## 2026-11-10 triage (P3 runner2 lane, work/p3-runner2-20261110): LIVE, out of lane (OS-kernel lane)

None of the four required-resolution items shows completion evidence on
this base (origin/release/1.0.0), and item 4 ("run the target QEMU
syscall-entry path; host interpreter tests alone do not prove the
C/assembly trap route") cannot be executed from a Windows seed-smoke lane
at all. Adjacent OS-kernel progress exists but does not claim this AC:
7e36d9a577aa ("thread Scheduler/IpcManager state across process
syscalls"), decd3c16f596 ("thread scheduler state through
dispatch_spawn_binary_direct"), 6788fd65c4c0 ("land the execve
capability/state-threading repair on the legacy leg") — all state
threading, none the trap-table resolution proof or the adversarial
per-class scenarios this bug requires.

Not fixed in this lane: the work is (a) owned by src/os kernel + target
QEMU verification, outside the test-runner lane's scope, and (b)
explicitly un-provable from host interpreter specs per the bug's own
required resolution item 4 — writing a host-only spec that purported to
satisfy it would be the dishonest-green pattern this ledger exists to
catch. Syscall dispatch/entry unit specs exist under
test/01_unit/os/kernel/ (syscall_dispatch_spec, syscall_entry_spec,
syscall_shim_*_spec) and remain the kernel lane's host-side evidence base.

Handed back to the OS-kernel lane with the AC table above as the
checklist.
