# Process Kill Safety — TL;DR

- tmux + all SSH + `systemd --user` dying same second = `kill(-1)` broadcast, **not OOM**. Journal shows `Activating special unit exit.target` and no OOM lines.
- Cause: failed spawn returns pid `-1`; unguarded cleanup `kill(pid)` then signals every user-owned process.
- Rule: every kill path (`kill()`, `waitpid()`, `shell("kill {pid}")`, `pkill -P`) must reject `pid <= 0` first.
- Guards landed in commit `4029a43d4ba8` (`rt_fork_parent_wait`, `native_process_kill`, `native_process_terminate`); other sites were already guarded.
- Seed caveat: Rust/C runtime guards reach deployed binaries only after seed rebuild + `bootstrap-from-scratch.sh --deploy`.
- Full guide: `process_kill_safety.md`
