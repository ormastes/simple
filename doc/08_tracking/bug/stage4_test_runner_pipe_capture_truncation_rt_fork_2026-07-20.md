# stage4 test-runner silently under-reports example counts — root cause: premature loop exit in `rt_fork_parent_wait_bounded` (runtime_fork.c)

Status: **root cause PROVEN via strace evidence; fix WRITTEN but NOT YET
VERIFIED** (rebuild died in the same session — see "Build breakage
encountered" below). Do not treat this as landed/closed.

## Summary

`test/01_unit/app/arch_check_spec.spl` has 74 unconditional `it` blocks
across 14 `describe` blocks (verified by reading the full file — no loops,
no guards, no skip markers). The Rust seed, run directly, reports
`Passed: 74, Failed: 0`. The self-hosted stage-4 binary's `simple test`
reports only **66** (default) or **18** (`--clean`, and independently also
`--no-self-protect`) — always fewer, never 74, and deterministic per flag
combination on repeat runs.

This is **not** a describe/it registration bug, **not** a module-loading or
cache bug, and **not** a bug in the spec file. It is a data-loss bug in the
native process-output-capture layer that `simple test` uses to read its
child's stdout/stderr.

## PROVEN: the child writes all 74 examples' worth of output to the pipe

Traced the real `simple test test/01_unit/app/arch_check_spec.spl` invocation
end-to-end with `strace -f -e trace=execve,write`:

1. The outer `simple test` process spawns, via `process_run_with_limits_bounded`
   (since `--max-mem-gb 16` is the default), the wrapped command:
   ```
   sh -c 'ulimit -v 16777216 ...; exec timeout --kill-after=5s 125s ./bin/simple run test/01_unit/app/arch_check_spec.spl'
   ```
2. `./bin/simple run <file>` (the self-hosted CLI) delegates file execution to
   its seed sibling via `cli_run_file` → `process_run_inherit` →
   `rt_process_spawn_async`, execing `./bin/simple_seed test/01_unit/app/arch_check_spec.spl`
   with **inherited** (not re-piped) stdio — i.e. the seed's stdout/stderr are
   the *same* pipe fds set up by the outermost fork.
3. Filtering the strace log for the seed's actual `write(1, ...)` syscalls and
   grepping for the `"N examples, M failures"` per-`describe` summary lines
   gives **exactly 14 writes** with values `5, 5, 4, 9, 3, 5, 8, 7, 3, 6, 5, 9,
   3, 2` — summing to **74**, matching the static count and the seed's own
   direct-run result precisely. The write syscalls are real, complete, and
   happen inside the same run that the parent later reports as "66 total".

This proves the *execution* is complete and correct under `simple test`'s own
real invocation; the loss happens strictly downstream, between the child's
`write()` and the parent's final parsed count.

## PROVEN: manual replication of the identical spawn never truncates

Reproduced the exact wrapped command captured by strace by hand (same
`ulimit`/`timeout`/env vars `SIMPLE_TEST_DEPTH=1 SIMPLE_RUNTIME_MODE=interpreter
SIMPLE_TEST_ASSERT_RAN=0 SIMPLE_SYSTEM_TEST=0 SIMPLE_DI_TEST=0`), invoked
directly via `sh -c` with the *shell's own* pipe/redirection (not through the
runtime's C capture code): **74/74, every time**, across several repeats. This
rules out anything about the spec file, delegation mechanism, or environment
variables — the only thing that changed between "genuinely 74" and "harness
reports fewer" is *which code reads the child's pipe*.

## PROVEN: the loss is timing-sensitive, not fixed

- Default flags (`simple test <file>`): **66/66/0**, deterministic across
  repeat runs (matches the task's prior-established fact).
- `--clean`: **18/18/0**, deterministic.
- `--no-self-protect` (no `--clean`): also **18/18/0**, deterministic.

Toggling `--self-protect`/`--clean` changes *how much pre-spawn work* the
parent does (daemon-connect probing, resource-governor `sh -c` probes) before
spawning the actual test child, which shifts the count. This is the signature
of a timing/scheduling race in the parent's pipe-drain logic, not a
content-dependent parser bug (a parser bug would not vary with unrelated CLI
flags that don't touch the spec file or its execution).

## Root cause: `rt_fork_parent_wait_bounded` in `src/runtime/runtime_fork.c`

`process_run_bounded`/`process_run_with_limits_bounded` (used by
`run_test_file_interpreter` in
`src/lib/nogc_sync_mut/test_runner/test_runner_execute.spl`) both bottom out
in `rt_process_run_bounded` → `posix_process_run_capture` →
`rt_fork_child_setup()` + `rt_fork_parent_wait_bounded()` in
`src/runtime/runtime_fork.c`.

`rt_fork_parent_wait_bounded`'s poll loop (pre-fix, around line 311-419 of the
original file) does:

```c
while (stdout_open || stderr_open) {
    if (!child_exited) {
        pid_t waited = waitpid_nointr((pid_t)child_pid, &child_status, WNOHANG);
        if (waited == (pid_t)child_pid) child_exited = 1;
    }
    ...
    int ret = poll(fds, nfds, poll_timeout);
    if (ret == 0) {
        if (child_exited) { cleanup_descendants = stdout_open || stderr_open; break; }  // <-- (A)
        continue;
    }
    /* read available chunks from ready fds ... */
    if (child_exited) { cleanup_descendants = stdout_open || stderr_open; break; }        // <-- (B)
}
```

`child_pid` is the PID of the **directly forked** process (`sh`/`timeout` in
our chain), not the actual writer of interesting content
(`bin/simple_seed`, reached three process-generations down via
`sh → timeout → bin/simple → bin/simple_seed`, all sharing the *same* pipe
write-end fd by inheritance). Once `waitpid(child_pid, WNOHANG)` observes the
tracked process has exited, both break sites (A) and (B) give the loop **at
most one more poll+read cycle** before unconditionally exiting — regardless of
whether `stdout_open`/`stderr_open` are still true (i.e. regardless of whether
either pipe has actually reached EOF). Site (B) is the more dangerous of the
two: it fires even when the *same* poll cycle just successfully read data
(`ret > 0`), i.e. even while data is actively still flowing.

The header comment on the file already states the correct intended behavviour
("Wake periodically to observe a child whose descendants retain pipe fds") —
the code does not do this; it treats the *first* post-exit cycle as final.
Recovery is left to a **single best-effort `drain_capture_fds()` call bounded
to 100ms**, gated on `cleanup_descendants` (only set when a stream was still
open at the break) — a much smaller and separately-raced safety net, not a
substitute for continuing the main drain loop.

This matches every observed symptom:
- Loss only happens under the real harness (extra process nesting + extra
  parent-side pre-work before spawn — self-protection probes, daemon-connect
  attempts — that shifts scheduling enough to change how much data survives
  the single post-exit drain pass).
- Loss never happens in a hand-run of the identical spawn command (no
  competing parent-side activity immediately around the spawn/read timing).
- Loss magnitude is deterministic per fixed flag combination but varies
  across flag combinations that change parent-side timing (`--clean`,
  `--self-protect`) without touching the spec or its true execution.

## Fix applied (WRITTEN, NOT VERIFIED)

`src/runtime/runtime_fork.c`, in `rt_fork_parent_wait_bounded`:

1. Removed break-site (B) entirely (the unconditional break right after a
   successful read-processing pass) — the loop now naturally continues via
   `while (stdout_open || stderr_open)` until both streams hit real EOF, are
   explicitly closed via `POLLERR`/`POLLNVAL`, or the pre-existing overall
   `timeout_ms` deadline fires (unchanged, still enforced every iteration).
2. Replaced break-site (A) (immediate break on the first no-data poll after
   child_exited) with a bounded grace counter
   (`FORK_EXIT_GRACE_POLLS = 40` × the existing 50ms `poll_timeout` ≈ 2s) —
   keep polling for up to ~2s of genuinely-idle pipes after the tracked
   child exits before giving up, instead of giving up on the very next empty
   poll.

Net diff is small (24 insertions / 6 deletions once the file's pre-existing
mixed CRLF/LF line endings are excluded via `git diff --ignore-space-at-eol`;
raw `git diff` is much larger purely from the Read/Edit tool round-trip
normalizing the whole file to LF — cosmetic, not semantic). Full semantic
patch saved at
`/tmp/claude-1000/-home-ormastes-dev-pub-simple/52b25380-3721-4826-b457-e1371d8b4cb5/scratchpad/runtime_fork_semantic_diff.patch`
for reference.

Safety: the change does not remove any bound on total wait time — the
existing `deadline_ms`/`timeout_ms` check (unchanged, checked every loop
iteration before each `poll()`) still caps worst-case duration; a genuinely
stuck descendant that never closes the pipe still gets killed by the
existing timeout path, not by an unbounded loop.

## Build breakage encountered while trying to verify (separate, likely
unrelated finding)

Rebuilding to test the fix requires `--full-bootstrap` (the C runtime is
compiled into `libsimple_runtime.a` via the Rust/cargo build, so a `.c`-only
edit still needs cargo to pick it up). This was attempted via
`scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --mode=dynload
--deploy` in `/tmp/wt_deploy`:

- Stage 2 and Stage 3 succeeded (with a stage2/stage3 sha256 mismatch flagged
  as "expected when runtime is embedded").
- **Stage 4 failed**: `build/bootstrap/logs/x86_64-unknown-linux-gnu/stage4-native-build.log`
  shows a **parser regression** on `src/app/cli/main.spl:15` — a plain
  `use std.cli.log_modes.{parse_log_options, log_options_help, render_progress}`
  braced-import-list statement, present in the file both before and after
  this session (confirmed via `git status`/`git diff` showing the file
  untouched) — fails with `expected field name after '.'`. The exact same
  source built cleanly at 13:05 (`1373 compiled, 0 cached, 0 failed`) earlier
  in this session, before `--full-bootstrap` forced a fresh cargo rebuild of
  the seed. This strongly suggests the freshly-rebuilt Rust seed's parser
  differs (regressed or was never actually validated against this grammar
  form in this exact build configuration) from whatever seed produced the
  13:05 binary — a **separate defect**, not caused by the one-line-class
  `runtime_fork.c` edit itself (a C file cannot change Simple-language
  grammar support). Investigating that regression is out of scope for this
  lane.
- The failed stage4-native-build also **deleted the previously-built**
  `build/bootstrap/full/x86_64-unknown-linux-gnu/simple` without replacing it
  (only `simple_seed` remains there now) — the rebuild pipeline does not
  preserve the last-good artifact on failure. This is itself worth a
  follow-up (a build step should not destroy a working deployable artifact
  before confirming the replacement built successfully).
- A backgrounded run of this same rebuild command (started before the
  environment's "do not background" constraint was made explicit) is
  confirmed dead — no live `bootstrap-from-scratch.sh`/`cargo`/native-build
  processes remain, and the log file stopped advancing at the stage4 failure
  above.
- **Confirmed reproducible, not flaky**: re-ran the bootstrap wrapper a
  second time in the foreground (bounded, `timeout 590`, no
  `--full-bootstrap` this time since "Seed/runtime current; skipping Rust
  rebuild" — reused the already-rebuilt seed and the already-cached
  stage2/stage3 artifacts from the dead run). Stage 4 failed **identically**
  (same `src/app/cli/main.spl:15:30` parser error, byte-for-byte same log
  tail) on the exact same, unchanged stage3 compiler. This rules out a
  one-off scheduling fluke and confirms the freshly-(cargo-)rebuilt seed's
  stage2/stage3 chain genuinely cannot parse `use a.b.{x, y, z}` braced-
  import-list syntax that the pre-existing (pre-session) stage-4 binary
  handled fine — a real toolchain regression, separate from and not caused
  by the `runtime_fork.c` semantic edit itself.

**Fallback baseline preserved**: two copies of the original (pre-fix, working)
stage-4 binary from before this rebuild attempt survive at
`/tmp/wt_deploy/release/x86_64-unknown-linux-gnu/simple` and
`/tmp/wt_deploy/bin/release/x86_64-unknown-linux-gnu/simple` (copied there
earlier in this session alongside a `simple_seed` sibling at
`release/x86_64-unknown-linux-gnu/simple_seed`, deployed via
`scripts/setup/setup.shs`). `bin/simple` / `bin/simple_seed` symlink to these
and still reproduce the original bug exactly (`Results: 66 total, 66 passed, 0
failed` on `test test/01_unit/app/arch_check_spec.spl`, re-confirmed just now)
— so the repro environment is intact for a future verification pass, but no
binary containing the `runtime_fork.c` fix has been produced or tested yet.

## Verification still required (not done)

1. A successful stage-4 rebuild containing the `runtime_fork.c` fix (blocked
   by the Stage 4 parser regression above — needs its own investigation or a
   workaround, e.g. building without `--full-bootstrap` if a way is found to
   get the fixed `.o` linked without a full cargo rebuild).
2. `simple test test/01_unit/app/arch_check_spec.spl` reporting `Results: 74
   total, 74 passed, 0 failed` in **both** default and `--clean` modes,
   matching the seed and the static `it` count.
3. Spot-check 2-3 other matrix specs (bdd, bitfield_sugar, fat32_cache,
   algorithm_utils) still report their exact static counts — this fix must
   not cause over-reading/duplication now that the loop can run longer.
4. Re-run `test_runner_bounded_output_contract_spec.spl` (the existing
   contract spec for this exact function family) — untouched by this fix
   (only the EOF/exit-timing control flow changed, not
   `capture_append`/`capture_finish`'s head/tail/marker math), but should be
   re-run as a direct regression gate.

## Files

- Fix: `src/runtime/runtime_fork.c` (`rt_fork_parent_wait_bounded`)
- Evidence: strace logs and manual repro logs under
  `/tmp/claude-1000/-home-ormastes-dev-pub-simple/52b25380-3721-4826-b457-e1371d8b4cb5/scratchpad/`
  (`strace_full.log`, `strace_execve.log`, `seed_direct.log`,
  `delegated_run.log`, `envrepro.log`, `ulimit_repro.log`)
- Related prior fix (different mechanism, already landed): commits
  `4581db7d8fd`/`c12f965ba50` and
  `doc/08_tracking/bug/stage4_test_runner_daemon_fallback_relint_nonmemoized_2026-07-20.md`
  (fixed a >900s hang caused by `app.io.mod` transitively pulling in the whole
  compiler; unrelated to the truncation bug documented here, which persists
  after that fix).
- Held fix commit: `9543d6f1aa3`. This commit lives in a **detached commit in
  `/tmp/wt_deploy`** — if that worktree is ever removed, the commit becomes
  unreachable and eligible for git GC. Do not treat this reference alone as a
  durable recovery path; the full patch is embedded below for exactly that
  reason.

### Full patch (embedded for durability — do not depend on the worktree commit or scratchpad above)

Copied verbatim from the semantic diff saved during the original (unverified)
fix session. Still **WRITTEN, NOT VERIFIED** — see the Status line at the top
of this doc. Applies to `src/runtime/runtime_fork.c`,
`rt_fork_parent_wait_bounded`, against the pre-fix baseline at
`src/runtime/runtime_fork.c` index `41cc9536cea`:

```diff
diff --git a/src/runtime/runtime_fork.c b/src/runtime/runtime_fork.c
index 41cc9536cea..e310e0170b4 100644
--- a/src/runtime/runtime_fork.c
+++ b/src/runtime/runtime_fork.c
@@ -309,4 +309,16 @@ int64_t rt_fork_parent_wait_bounded(int64_t child_pid, int64_t timeout_ms,
     }
 
+    /* Grace polls after the tracked child_pid is reaped: a delegated driver
+     * binary (e.g. bin/simple execing/inheriting fds down to bin/simple_seed)
+     * can still hold the pipe write end open via an inherited fd for a few
+     * scheduler ticks after the directly-forked process (sh/timeout) exits
+     * and is reaped. Breaking on the very next poll cycle after child_exited
+     * silently drops whatever a still-writing descendant produces after that
+     * point -- verified via strace that the descendant DOES write its full
+     * output to the pipe, yet callers observed truncated captures. Cap the
+     * grace period so a genuinely stuck descendant can't hang the caller. */
+    int exited_grace_polls = 0;
+    const int FORK_EXIT_GRACE_POLLS = 40; /* ~2s at the 50ms poll_timeout below */
+
     while (stdout_open || stderr_open) {
         if (!child_exited) {
@@ -353,9 +365,13 @@ int64_t rt_fork_parent_wait_bounded(int64_t child_pid, int64_t timeout_ms,
         if (ret == 0) {
             if (child_exited) {
-                cleanup_descendants = stdout_open || stderr_open;
-                break;
+                exited_grace_polls++;
+                if (exited_grace_polls >= FORK_EXIT_GRACE_POLLS) {
+                    cleanup_descendants = stdout_open || stderr_open;
+                    break;
+                }
             }
             continue;
         }
+        exited_grace_polls = 0;
 
         /* Process events */
@@ -397,8 +413,10 @@ int64_t rt_fork_parent_wait_bounded(int64_t child_pid, int64_t timeout_ms,
             }
         }
-        if (child_exited) {
-            cleanup_descendants = stdout_open || stderr_open;
-            break;
-        }
+        /* Do NOT break here just because child_exited: this poll cycle just
+         * made progress (ret > 0), so a descendant may still be writing.
+         * Let the outer `while (stdout_open || stderr_open)` loop continue
+         * driving reads until both streams hit real EOF, or the grace-poll
+         * counter above (for the no-progress case) or the overall timeout
+         * deadline bounds the wait. */
     }
 
```
