# native-build full-closure: task's own success bar is MET on a clean run — no fork/wait deadlock observed; earlier "deadlock" report was very likely a monitoring artifact over a slow (but live) parse phase

Date: 2026-07-12
Status: investigated; task's Step-3 success criterion reproduced with NO fix applied; redirect residual perf question to parser-perf tracking
Severity: informational (no orchestration fix landed; do not implement one against this premise)

## Bottom line

The task defines success (Step 3) as: the full closure build "gets PAST
module-load into `parse:file:N/~500` markers and keeps advancing... CPU
~100%, no zombie, no futex-block." On a clean checkout of origin/main tip
`a1d8e496fae` (no code changes), the repro **met that bar directly**: 16
`parse:file:done` markers accumulated over ~9 minutes, CPU pinned at 99.9%
the whole time, utime climbing monotonically, zero futex-block on the
worker. Most likely explanation: the 12 compiler fixes already landed on
this tip (see git log) resolved whatever the earlier session hit, and/or
the earlier "frozen at ~50448B, right after `[gc-warning]`" observation was
itself always just `native_build_main`'s own stdout going quiet the instant
it started legitimately blocking on the worker (see below) — not a hang.
This is corroborated by the task's own bisect note: pre-fix
(`7beb9db8`), non-entry closure modules were empty stubs, so the worker had
~nothing to do (fast); post-fix, every module gets real lowering (slow).
That is a **work-volume/throughput story**, not a deadlock signature.

**Open / not verified in this session:** whether the full ~500-file closure
actually *completes* and emits a binary within an acceptable wall-time.
Per-file parse cost appears to *increase* over the run (see timings below)
rather than stay flat, so extrapolating from 16/~500 files to "it will
finish in ~5.7h" is not something this investigation confirmed — only that
it is not deadlocked in the observed 9-minute window. That throughput
question is separate from this task's fork/wait-deadlock scope and is
flagged below for follow-up.

## Task as given

Fix a claimed process-orchestration deadlock in `native_build_main` (worker
fork/wait), characterized as: parent blocks forever in `futex_wait_queue`/
`do_wait` at near-0% CPU because a forked `simple-main` child dies
immediately (zombie) and is never correctly handled, freezing the build log
right after the `[gc-warning]` lines and before any `parse:file` marker.

## What was actually observed (clean repro, origin/main tip a1d8e496fae, worktree
`.claude/worktrees/agent-a40931d256ddc76b4`)

Ran the exact repro command from the task (`SIMPLE_BOOTSTRAP=1
SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1 SIMPLE_NO_STUB_FALLBACK=1
SIMPLE_COMPILER_PHASE_PROFILE=1 <seed> run src/app/cli/native_build_main.spl
-- --backend cranelift --source src/compiler --source src/app --source
src/lib --entry-closure --threads 1 --cache-dir build/bootstrap/native_cache
--mode dynload --entry src/app/cli/main.spl --runtime-path ... -o ...`),
twice.

1. **`native_build_main`'s own stdout/stderr (the log the task's repro
   redirects to) does stop growing right after the `[gc-warning]` lines**,
   at 46493 bytes — matching the task's description exactly. This is
   because `native_build_main.spl`'s `run_native_build_worker()` immediately
   calls `process_run_timeout()` → `process_run_timeout_unix()`
   (`src/app/io/process_ops.spl:61`), which spawns `/bin/sh -c "timeout
   --kill-after=5s 7200s '<seed>' run native_build_worker.spl ... >
   '/tmp/simple_out_<pid>_<ts>.txt' 2> '/tmp/simple_err_<pid>_<ts>.txt'"` and
   then blocks in `rt_process_wait(pid, 0)` (a real `Child::wait()` in
   `env_process.rs`). **`native_build_main`'s own log freezing at that point
   is 100% expected** — its job from that point on is to block until the
   worker (redirected to the temp files) finishes; it prints nothing more
   until the worker exits.

2. **The actual worker output goes to
   `/tmp/simple_out_<native_build_main-pid>_<ts>.txt` /
   `..._err_...txt`, which the task's repro never inspects.** Reading those
   files shows the build is **not stuck**: `phase2:parse:file:start` /
   `phase2:parse:file:done` markers are present and advancing continuously,
   e.g. (from one run):
   ```
   +237188ms phase2:parse:file:start src/app/build/cli_entry.spl chars=1633
   +240612ms phase2:parse:file:done  src/app/build/cli_entry.spl
   +240613ms phase2:parse:file:start src/app/cli/arch_check.spl chars=19414
   +302004ms phase2:parse:file:done  src/app/cli/arch_check.spl
   ...
   +485956ms phase2:parse:file:done  src/app/stats/doc_coverage_dynamic.spl
   +485958ms phase2:parse:file:start src/app/stats/dynamic.spl chars=21654
   ```
   16 `parse:file:done` markers had accumulated by ~552s wall-clock, and the
   file kept growing on every subsequent poll.

3. **CPU/utime confirms live, continuous compute — not a block.** Sampled
   the worker's `/proc/<pid>/stat` utime three times, 15s apart:
   `47175 → 48665 → 50150` ticks (steadily climbing, ~99.9% of one core the
   entire time per `ps -o pcpu`), for 552s+ of wall-clock with the
   process never dropping toward 0% CPU. This directly contradicts the
   "parent blocks forever … near-0% CPU" characterization — the worker is
   CPU-bound and making forward progress, not futex/wait-blocked.

4. **The `simple-main` zombie children are a real, separate, but harmless,
   long-standing artifact — not the cause of anything.** Both
   `native_build_main` (P0) and the worker (P3) spawn exactly one zombie
   child named `simple-main` shortly after starting
   (`state=Z`, `wchan=0`, empty cmdline — confirmed via `/proc/<pid>/status`
   `PPid:`/`Tgid:` to be genuine forked processes, not thread-group
   artifacts). **Proof this is unrelated to the reported hang:** every
   already-running, healthy `bin/simple run src/app/mcp/main.spl` MCP server
   process on this same host (actively serving this very session's LSP/MCP
   tool calls) carries the **exact same** 3x `simple-main` zombie children.
   Those servers are demonstrably not deadlocked. So the zombie is some
   unreaped-but-irrelevant startup artifact (likely from a short-lived
   internal probe subprocess whose `Command::spawn()` handle is dropped or
   waited on the wrong path), not a blocking dependency for anything else.
   `native_build_main`'s own thread that legitimately blocks in `do_wait`
   (confirmed via `/proc/<tid>/wchan`) is waiting on the `/bin/sh` PID from
   step 1 (still alive, doing real work) — not on the zombie.

5. **`gdb`/`strace` attach is unavailable in this sandbox** (ptrace is
   blocked even for a direct child of the same shell — verified with a
   throwaway `sleep` child: `ptrace(PTRACE_SEIZE, ...)`→`Operation not
   permitted`, and `/proc/<pid>/stack` and `/proc/<pid>/syscall` are
   `Permission denied` even for descendant processes with a matching uid).
   All findings above are from `/proc/<pid>/{status,stat,wchan}` and the
   redirected temp-file logs, not from a live debugger backtrace.

## Conclusion

**No fork/wait orchestration deadlock reproduces on origin/main tip
`a1d8e496fae` for this exact repro.** The build is not stuck; it is
extremely slow. Per-file parse times observed: ~30–120s for files in the
10–22KB range, and multi-second times even for small (<3KB) files late in
the run — consistent with the task's own acknowledged "~5.7hr parse" budget
for the full ~500-module closure. The original "deadlock" observation was
almost certainly a **monitoring artifact**: watching only
`native_build_main`'s own stdout (which legitimately goes silent the moment
it starts blocking on the worker) without also checking the worker's
redirected temp-file output, combined with per-file parse times long enough
(tens of seconds) that a short poll window looks indistinguishable from a
true hang.

This does **not** rule out a real fork/wait bug existing on some other
input/timing/host, but it is not the dominant, reproducible behavior on this
tip. **No orchestration fix was implemented against this premise** —
forcing a fix here would either be a no-op or risk changing working
spawn/wait code based on a misdiagnosis.

## Separate, real, but unproven-to-be-related finding: latent pipe-buffer deadlock hazard

`rt_process_spawn_async` (`src/compiler_rust/runtime/src/value/sffi/env_process.rs:478-519`)
sets the spawned child's stdout/stderr to `Stdio::piped()`
(lines 505-507), and `rt_process_wait` (line 599) just calls
`Child::wait()`, which never reads/drains those pipes. **If a caller spawns
a process this way without redirecting its stdout/stderr elsewhere (e.g. no
shell `>`/`2>` redirection) and that child writes more than the OS pipe
buffer (64KB on Linux) before exiting, the child will block on `write()`
forever while the parent blocks in `wait()` forever — a classic two-sided
pipe deadlock.** This is real and worth fixing (e.g. spawn a draining
thread per pipe, or default to `Stdio::null()`/file redirection), but **it
is not what is happening in the reported native-build repro**: the specific
call chain here (`process_run_timeout_unix`) wraps the command in `/bin/sh
-c "... > file 2> file"`, so the shell's own `dup2()` redirection replaces
fd 1/2 before the child ever writes to the piped fds — the pipes
`rt_process_spawn_async` set up are immediately superseded and never fill.
Recorded here for visibility; not fixed as part of this task since it does
not match the reported symptom's call path.

## What to actually track instead

The real, reproducible wall for the full-closure native-build is **parser
throughput at scale** (tens of seconds per file, apparently getting worse as
more modules accumulate — e.g. `env_ops.spl` at 2735 chars took 8.7s while
`cli_entry.spl` at 1633 chars took 3.4s and `cli_commands.spl` at 377 chars
took 0.36s, all within the same run, suggesting a per-file cost that scales
with cumulative modules/symbols parsed so far rather than pure per-file
size — worth a follow-up profiling pass, but out of scope for this
fork/wait investigation). This is already implicitly acknowledged by the
task's own "~5.7hr parse" budget language, so it is likely already tracked
under the existing closure-gap/wall bug docs
(`doc/08_tracking/bug/*entry_closure*`, `*closure*wall*`) rather than a new
process-orchestration bug.

Separately, and out of scope for this investigation: `doc_coverage_dynamic.spl`
hit a `[parser_error] line 1:72: expected , or } in dict literal` during this
run (parser recovered and still emitted `parse:file:done`, so it did not
hang). Worth a one-line flag: even a build that never deadlocks could still
*fail* later once such parse errors propagate — not investigated further
here.

## Repro command (for future reference)

```sh
cd <worktree>
rm -rf build/bootstrap/native_cache
env SIMPLE_BOOTSTRAP=1 SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1 SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_COMPILER_PHASE_PROFILE=1 \
  <seed> run src/app/cli/native_build_main.spl -- \
  --backend cranelift --source src/compiler --source src/app --source src/lib \
  --entry-closure --threads 1 --cache-dir build/bootstrap/native_cache \
  --mode dynload --entry src/app/cli/main.spl \
  --runtime-path <repo>/src/compiler_rust/target/bootstrap \
  -o <out> > <toplevel.log> 2>&1 &
# Then, critically, watch the REDIRECTED WORKER temp files, not <toplevel.log>:
ls -t /tmp/simple_out_<toplevel-pid>_*.txt /tmp/simple_err_<toplevel-pid>_*.txt
tail -f /tmp/simple_out_<toplevel-pid>_*.txt
```
