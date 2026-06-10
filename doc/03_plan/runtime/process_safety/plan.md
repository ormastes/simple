# Plan: Process Kill Safety — Crash Fix Rollout

Status: guards landed on main (commit `4029a43d4ba8`, 2026-06-10).
Background: `doc/07_guide/runtime/process_kill_safety.md` (session-killing
`kill(-1)` broadcasts on 2026-06-08 ×3 and 2026-06-10).

## Done

- [x] Diagnose crash signature (journal: exit.target + simultaneous SSH/tmux
      teardown; OOM/network/logind ruled out).
- [x] Audit all kill paths in repo (C runtime, Rust runtime, `.spl` libs,
      `.shs` scripts, test runner, kill monitor).
- [x] Guard `rt_fork_parent_wait` (`src/runtime/runtime_fork.c`) — `child_pid <= 0 → -1`.
- [x] Guard `native_process_kill` (`runtime/src/value/file_io/process.rs`).
- [x] Guard `native_process_terminate` (`runtime/src/value/process.rs`).
- [x] Verify: `gcc -fsyntax-only` + `cargo check -p simple-runtime` clean.
- [x] Guide + TLDR under `doc/07_guide/runtime/`; spipe skill exception note.

## Remaining

- [ ] Rebuild Rust seed (`cd src/compiler_rust && cargo build --profile bootstrap -p simple-driver -p simple-native-all`)
      so interpreter-mode `bin/simple` carries the Rust-side guards.
- [ ] `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` so the
      self-hosted `bin/release/<triple>/simple` carries the C-runtime guard
      (`rt_fork_parent_wait`).
- [ ] After next multi-day parallel-agent session: confirm no recurrence of
      the journal signature (`Activating special unit exit.target` on the
      user manager outside reboots).

## Non-goals

- OS-level prevention of `kill(-1)` — POSIX allows a user to signal their own
  processes; the defense is guards at every kill call site.
- Lint automation for unguarded kills — revisit only if a new incident shows
  the manual rule is insufficient.
