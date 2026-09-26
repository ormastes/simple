# Windows: a bootstrap loses the Rust authority lock while another worktree runs seed/cargo builds

- **Date:** 2026-09-25
- **Status:** OPEN
- **Area:** bootstrap / `scripts/check/lib/portable-process-lock.shs` / Windows (MSYS)

## Observed

- bootstrap37 (`D:/wk-bs2-20260924`) aborted during an otherwise successful Rust seed build with
  `error: Rust authority lock ownership was lost`
  - The message comes from `scripts/bootstrap/bootstrap-from-scratch.sh:2223`.
  - It fires when `bootstrap_authority_require_owned_lock` / `portable_lock_handle_is_owned` fail.
- At the same time, other `git worktree`s of the same clone (`C:/Users/ormas/dev/simple`) were running seed
  (cargo) builds and stage-2 compiler probes.
- The coordinator's reading is that on Windows the lock is effectively repo-wide, shared by every worktree of
  the clone. After the other worktrees stopped building, bootstrap38 was relaunched.

## Why it is a bug

A second worktree must never be able to take a live owner's lock silently. At most it should wait, or refuse
loudly. An owner that finds its lock gone mid-build cannot tell a crash from theft, so the only safe response
is to abort, which wastes the whole run.

## Where to look (not yet verified)

- **Lock root:** `bootstrap-from-scratch.sh:2215` puts it under
  `${repo_root}/src/compiler_rust/target/.bootstrap-authority-locks`.
  - Establish whether that directory is really shared across worktrees on this host.
  - Check junctions, the materialized symlinks under `src/compiler_rust`, and a `CARGO_TARGET_DIR` shared
    through the environment.
- **Stale-claim recovery** (`portable_lock_acquire`):
  - A claim is recovered when `portable_lock_claim_state <pid> <start> <pgid>` answers `dead`.
  - Under MSYS, a live owner's pid / start time / process group may not be observable from another process
    tree. The owner is then judged `dead` and its claim is recovered from under it.
  - This is the leading hypothesis. Reproduce it with two shells, one holding the lock and one acquiring it,
    and print `portable_lock_claim_state` for the holder.

**Done when:** a second acquirer on Windows blocks or fails with a named owner while the first owner is alive.
There should be a selftest fixture in `portable-process-lock.shs` that holds a claim in one process and
acquires from another.

## Related: seed-delegated `run` exits 127 after passing

- **What happened:** the stage-2 full CLI's `run <spec>` delegates to the cwd `bin/simple.exe` (the Rust
  seed) unless `SIMPLE_NO_BOOTSTRAP_DELEGATE=1` is set.
  - Measured 2026-09-25: `check_entry_target_routing_contract_spec.spl` printed `2 examples, 0 failures` and
    `SPEC FILE VERDICT ... outcome=OK`, then the process exited 127.
  - The test runner reported TERM for it.
- **Now:** phase verification sets `SIMPLE_NO_BOOTSTRAP_DELEGATE=1`, so this path no longer affects the
  stage-2 test matrix.
- **Still open:** the 127 after a passing delegated run is not explained. Suspects are the seed's exit path or
  `process_run_inherit` on Windows mapping a missing exit status to 127.
