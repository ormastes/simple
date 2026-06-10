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

- [x] Rebuild Rust seed (`cd src/compiler_rust && cargo build --profile bootstrap -p simple-driver -p simple-native-all`)
      so interpreter-mode `bin/simple` carries the Rust-side guards.
      (Done 2026-06-10 07:38; seed deployed to `bin/release/x86_64-unknown-linux-gnu/simple` 09:18.)
- [x] `scripts/bootstrap/bootstrap-from-scratch.sh --deploy` — ran 2026-06-10
      (script restored from git history after deletion in `4cf561567f`; helper
      paths repointed to `scripts/setup/*.shs`). Stage 2 OK, stage 3 known-fail
      (LIM-010), but the stage-4 cranelift full-CLI binary it deployed
      **re-execs itself in a loop** when given a `.spl` file (fork bomb;
      see BUG below). Reverted the deploy to the freshly built Rust seed,
      which carries the Rust-side guards. The C-runtime guard
      (`rt_fork_parent_wait`) is not linked into `bin/simple` at all — it is
      compiled fresh from `src/runtime/runtime_fork.c` by
      `compile_runtime_objects` whenever a native binary is linked, so every
      future native build picks up the guard from source automatically.
- [ ] BUG: stage-4 (`seed native-build --backend cranelift --entry
      src/app/cli/main.spl`) produces a 15.8 MB binary that exec-loops on
      `simple <file.spl>` / `simple run` (thousands of self-respawns;
      `--version`/`--help` work). Artifact kept at
      `build/bootstrap/full/x86_64-unknown-linux-gnu/simple`. Fix the
      full-CLI self-exec/wrapper dispatch before the next self-hosted deploy.
- [ ] After next multi-day parallel-agent session: confirm no recurrence of
      the journal signature (`Activating special unit exit.target` on the
      user manager outside reboots).

## Non-goals

- OS-level prevention of `kill(-1)` — POSIX allows a user to signal their own
  processes; the defense is guards at every kill call site.
- Lint automation for unguarded kills — revisit only if a new incident shows
  the manual rule is insufficient.
