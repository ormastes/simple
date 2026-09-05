# Plan — CLI self-delegation fix → redeploy

**Date:** 2026-07-25 · **Status:** source fixes landed (`6cf217f0febb`, superseded by `0531ca8ce266`); redeploy outstanding

## Why this plan exists

`bin/simple run <file>` is currently an unbounded self-delegation loop. Root
cause and the corrected code are recorded in
`doc/08_tracking/bug/cli_symlink_argv0_seed_sibling_lookup_2026-07-24.md`
(§ Correction 2026-07-25). Everything below is what remains *after* that fix
landed.

The fix is source-only. The deployed
`bin/release/x86_64-unknown-linux-gnu/simple` (built 02:05, 2026-07-25)
predates it, so `run` / `lint` / `test` stay unusable until a redeploy. **No
part of the fix has been executed** — the evidence is a direct probe
(`/proc/self` → `/usr/bin/readlink`, `/proc/$PPID` → the real binary), not a
passing test.

## Remaining work

| # | Item | Blocked by | Owner |
|---|---|---|---|
| 1 | Redeploy the self-hosted CLI | seed regression `d312b8e4253` | dedicated bootstrap session |
| 2 | Execute the regression spec | #1 | follows #1 |
| ~~3~~ | ~~Dead `_cli_resolve_symlink` guard~~ | — | **done** `0531ca8ce266` |
| 4 | Stale-WC clobber exposure | ongoing parallel sessions | standing hazard |

### 1. Redeploy (the blocker for everything else)

A seed built from HEAD cannot native-build any `.spl` ("expr_tag OOB parse
file 1"), so the seed must come from before the regression:

1. Build the Rust seed from **`906b85d1420`** (pre-`d312b8e4253`):
   `cargo build --release --bin simple --features llvm` in that worktree.
   Do **not** use `e042a9d222b` — pre-regression but lacks literal interning,
   so parse balloons to ~101 GB.
2. Stage that seed at `src/compiler_rust/target/bootstrap/simple` of a
   **main-tip** worktree (main carries interning + the borrow-check workaround).
3. `sh scripts/bootstrap/bootstrap-from-scratch.sh --backend=cranelift --full-bootstrap --deploy`

Expected stage4 peak ~18 GB with the interning fix (never yet run to
completion — the ~18 GB figure is projected, not observed). The
`kill_simple_monitor.shs` 64 GB cap should not trip at that size; if it ever
does, the unblock is a lowercase `claude` token in argv[0], not an env var.

### 2. Verify after redeploy

- `bin/simple run <any .spl>` terminates (the loop is gone)
- `bin/simple test test/01_unit/app/io/cli_argv0_resolution_spec.spl` — the
  "resolves our own exe, not the spawned readlink helper" and "establishes its
  own identity in-process" cases actually run
- The fork-bomb guard bites: `_cli_is_current_exe("bin/simple")` must be **true**
  when running as `bin/release/<triple>/simple`. This is the check that was
  silently disarmed; a redeploy that leaves it false has not fixed anything.
- `bin/simple lint <file>` — confirms the `field access on nil receiver`
  symptom was stale-binary only. The source fix is already in place
  (`src/compiler/55.borrow/borrow_check/nll.spl:392,404` use
  `borrowset_active_list(...)`; zero `.active_borrows()` calls remain), so a
  recurrence after redeploy means a *different* defect.

### 3. Dead assertion — RESOLVED 2026-07-25 (`0531ca8ce266`)

**Verdict: dropped fix, not a stale guard. The assertion was right; the code had
regressed past it.** Restoring `_cli_resolve_symlink` made all nine of the
spec's source-text assertions pass again.

`_cli_is_current_exe` compares a delegation candidate against our real exe.
`bin/simple` is a symlink to `bin/release/<triple>/simple`, so with the
candidate left unresolved the comparison never matched — the fork-bomb guard
was reporting "that isn't me" about itself and waving the delegation through.
It was the second line of defence against the very loop this plan exists for,
and it had been silently disarmed since 2026-07-24.

This also **superseded the `$PPID` shell-out** from `6cf217f0febb`.
`_cli_resolve_symlink` wraps `rt_path_absolute` = `std::fs::canonicalize`,
called **in-process**, so `/proc/self/exe` resolves to our own binary with no
spawn at all — no PPID hop to be off by a level, and the helper-basename
denylist became dead code and was removed. Verified by probe:
`rt_path_absolute("/proc/self/exe")` → the running binary;
`rt_path_absolute("bin/simple")` → its symlink target. All four sites converted;
zero shell-out identity reads remain in `src/`. No new Rust extern was needed.

<details><summary>Original framing (kept — the reasoning is why the answer wasn't obvious)</summary>

`test/01_unit/app/io/cli_argv0_resolution_spec.spl:41` asserts the source
contains `val resolved = _cli_resolve_symlink(path)`. That function exists
nowhere in `src/` — only in this assertion and two bug docs. History shows it
was real and then removed, superseded by the `/proc/<pid>/exe` approach.

Two readings, and they lead opposite ways:

- **Stale guard** (likely): repoint it at the current implementation.
- **Dropped fix**: `_cli_resolve_symlink` was load-bearing for
  `cli_driver_binary_symlink_argv0_2026-07-11.md` and its removal regressed
  that case — restore the function.

Interpreter mode does not execute `it` bodies, so this may not be *failing*
today; it is dead either way. Do not guess — resolve against the 07-11 bug doc.

</details>

### 4. Standing hazard — stale WC reverts landed fixes

This tree hosts concurrent sessions. During this work a parallel session
reverted all four `$PPID` one-liners minutes after they were written (the
helper functions survived; the one-liners did not), and afterwards `@` was left
parented on a **pre-fix** commit while origin already had the fix — arming a
whole-WC sync to revert it.

Two habits this cost:

- Re-verify edits by grep after any concurrent activity; the Edit tool
  reporting success is not proof the content is still there.
- After a scoped `jj commit <paths>`, **check `@`'s parent**. A green push does
  not mean the working copy is safe. Merge forward
  (`jj rebase -r @ -d main@origin`) rather than reverting, and confirm the other
  session's in-flight files are byte-identical afterwards.

## Related

- `doc/08_tracking/bug/cli_symlink_argv0_seed_sibling_lookup_2026-07-24.md` — root cause + correction
- `doc/08_tracking/bug/cli_driver_binary_symlink_argv0_2026-07-11.md` — the `_cli_resolve_symlink` origin, needed for item 3
- `doc/03_plan/compiler/bootstrap/redeploy_stage4_plan_2026-07-09.md` — prior stage4 redeploy plan
