# Fork mode is crash containment, not fresh-process-per-unit

**Status:** design note, no code change. **Date:** 2026-08-18. **Lane:** FORK.
**Scope:** `src/lib/nogc_sync_mut/test_runner/test_runner_fork.spl`,
`src/runtime/runtime_fork.c`, `src/compiler_rust/.../env_process.rs`.

## What fork mode actually is (file:line evidence)

- Fork **without exec**. `src/runtime/runtime_fork.c:2` states it in the header
  ("Fork-without-exec implementation for test runner isolation"); `:218` is the
  sole `fork()`; there is **no `exec*` call anywhere in the file** — the only
  other process-lifecycle call is `_exit()` (`:43`, `:593-594`).
- The child re-enters the parent's already-loaded interpreter directly:
  `test_runner_fork.spl:126` `rt_cli_run_file(file_path, args, ...)`, guarded by
  `:121 if pid_or_zero == 0`, then `:127 rt_fork_child_exit(result)`.
- Wiring: `test_runner_execute.spl:90` dispatches to `run_test_file_fork` when
  `options.fork_mode`; flag set at `test_runner_args.spl:470` (`--fork` /
  `--fork-mode`), cleared at `:473` (`--no-fork`). Default false (`:273`).

So: **a child process per spec, COW-inherited from the parent image. Not a
fresh process.**

## Outcomes are classified, not collapsed

`classify_fork_exit` (`test_runner_fork.spl:73-94`) is called ahead of
`make_result_from_output` (`:162-163`) and maps waitpid's real status:
`TIMEOUT:` (`:80`), `TERMINATED:` for outside-kill signals SIGHUP/SIGINT/
SIGKILL/SIGTERM with `failed: 0` (`:71`, `:86`), `CRASHED:` with `failed: 1`
for fault signals (`:87`), `TERMINATED:` unverified for an unreapable child
(`:92`). This half of the contract is met, and fork mode is strictly better
than the subprocess path here: `rt_fork_parent_wait` returns `128 + WTERMSIG`
(`runtime_fork.c:463-465`) where `env_process.rs:508,535` collapses every
signal **and** timeout into a single `-1`.

## Verdict: COW-inherit is NOT adequate for unstable mode

Unstable mode promises a separate process per unit so that a poisoned
interpreter cannot contaminate the next unit. A COW fork inherits module
tables, caches, globals and any corrupted heap **at the moment of the fork**,
and the parent is the accumulator: unit N+1 forks from a parent that has
already loaded and mutated state for units 1..N. Crash containment holds
(the child dies, the suite continues); state freshness does not. These are
different guarantees and only the second is what unstable mode was defined as.

## The exact change required (not made here — it is not small)

The tempting fix, "make the fork child exec `bin/simple` on the spec", deletes
fork mode's only advantage (speed: no binary load) and reproduces the existing
subprocess path. The correct change is the reverse:

1. **Lift signal fidelity into the subprocess path.** Replace the `-1` sentinel
   in `src/compiler_rust/.../env_process.rs:508,535` with `128 + WTERMSIG` on
   `WIFSIGNALED`, and a distinct sentinel for timeout. This requires a seed
   rebuild and is the only runtime change needed.
2. **Then make unstable mode refuse `--fork`.** With (1) done, the subprocess
   modes give both fresh-process-per-unit *and* the real signal number, so
   `--unstable --fork` should be a hard argument error rather than a silently
   weaker run.
3. **Until (1) lands**, keep fork mode opt-in and off by default, and treat a
   fork-mode unstable run as weaker evidence — as the header comment at
   `test_runner_fork.spl:10-19` already records.

Nothing in step 1 or 2 belongs to this lane's file, and doing half of it (e.g.
adding an exec to the fork child) would be strictly worse than the status quo.

## Evidence limitation (honest)

This could not be demonstrated by a real run on this host. See
`doc/08_tracking/bug/fork_mode_unreachable_on_deployed_seed_2026-08-18.md`:
the deployed `bin/simple` contains **zero** `rt_fork*` strings (control:
`rt_cli_run_file` = 12 hits, `rt_string_concat` = 5), so the fork SFFI bridge
is not present in the binary at all, and the attempted run produced 364 lines
of warnings with zero result lines — the known silent-green defect. Separately,
no `.spl`-only crash fixture exists: unbounded recursion is caught by the
interpreter's depth guard and reported as an ordinary failing example, not a
signal death. Every claim above is therefore source-level (file:line) and
explicitly **not** run-verified; in particular `classify_fork_exit` has never
been observed executing.
