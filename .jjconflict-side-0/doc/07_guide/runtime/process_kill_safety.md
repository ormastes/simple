# Process Kill Safety — pid Guards Against `kill(-1)` Broadcast

## The incident (2026-06-08, 2026-06-10)

Heavy parallel agent/test sessions were "crashing": tmux server, all SSH
sessions, and `systemd --user` died in the same second. Journal signature:

```
systemd[<user-mgr>]: Activating special unit exit.target...   # = got SIGTERM
sshd[...]: pam_unix(sshd:session): session closed (×N, same second)
systemd[1]: user@1000.service: Deactivated successfully       # clean exit
```

Ruled out: kernel OOM, systemd-oomd, coredumps, network drop (no sshd
disconnect reasons), logind cleanup (`Linger=yes`, `KillUserProcesses=no`,
PID 1 never logged "Stopping user@1000"). The only mechanism matching the
signature is `kill(-1, SIGTERM)` — POSIX defines pid `-1` as *every process
the caller may signal*. pid `0` signals the caller's whole process group.

## Root cause pattern

Spawn/fork failure returns pid `-1`; cleanup code later kills the stored pid
without a guard:

```c
pid_t pid = fork();          /* -1 on failure */
...
kill((pid_t)pid, SIGKILL);   /* pid == -1 → kills EVERYTHING you own */
```

## The rule

**Every kill path — shell or native — must reject `pid <= 0` before
signalling.** This includes `kill()`, `waitpid()` (pid `-1` reaps any child),
`shell("kill {pid}")` interpolation, and `pkill -P {pid}`.

Guarded sites (as of commit `4029a43d4ba8`):

| Site | Guard |
|------|-------|
| `src/runtime/platform/unix_common.h` `rt_process_kill` / `rt_process_is_running` | `pid <= 0 → false` (pre-existing) |
| `src/runtime/platform/platform_win.h` `rt_process_kill` | `pid <= 0 → false` (pre-existing) |
| `src/runtime/runtime_fork.c` `rt_fork_parent_wait` | `child_pid <= 0 → -1` |
| `src/compiler_rust/runtime/.../file_io/process.rs` `native_process_kill` | `pid <= 0 → NIL` |
| `src/compiler_rust/runtime/.../process.rs` `native_process_terminate` | `pid <= 0 → false` |
| `src/lib/*/debug/remote/exec/adapter_*.spl` shell kills | `if self.*_pid > 0:` (pre-existing) |
| `src/app/test_runner_new/process_tracker.spl` | registers only `pid > 0` (pre-existing) |

For new code: in `.spl`, guard before any `shell("kill ...")` or
`process_kill` call when the pid came from a spawn that can fail; in the seed
runtime (Rust/C), guard at the function entry, mirroring `rt_process_kill`.

## Deployment caveat

The Rust crate and C runtime are the **seed** — guards there reach running
binaries only after a seed rebuild (`cargo build` in `src/compiler_rust`) and
`scripts/bootstrap/bootstrap-from-scratch.sh --deploy`. Until redeploy, the
deployed `bin/simple` carries the old code.

## Diagnosing a recurrence

If tmux + all SSH sessions die at once, do **not** assume OOM. Check:

```bash
journalctl --since "<time-2min>" --until "<time+2min>" | grep -E "exit.target|session closed|oom"
journalctl -k | grep -i oom          # kernel OOM (was empty in both incidents)
```

Simultaneous teardown + `exit.target` + no OOM lines = pid broadcast; audit
recently added kill/cleanup paths.
