# native-build parent hangs forever when its worker dies early (zombie, empty log)

Date: 2026-07-03
Status: REOPENED — parent interruption still leaks the nested timeout/worker
Severity: P1 (blocks bootstrap stage 4 / --deploy on this host; silent 2h timeout burns)
Found by: fable orchestrator during bootstrap redeploy

## Fix (2026-07-03)

`src/app/io/process_ops.spl`: `process_run_timeout_unix` no longer captures
worker output through `rt_process_run`'s blocking `popen()`/`fgets()` pipe
read (which only returns on pipe EOF and hangs forever if an orphaned
grandchild inherits the write end); it now spawns `timeout --kill-after=5s
<secs>s <cmd> <args>` asynchronously via `rt_process_spawn_async` with
stdout/stderr redirected to temp files, and reaps it with a single blocking
`rt_process_wait(pid, 0)` — bounded by `timeout`'s own guarantee, not by pipe
EOF, and file reads never block on another process's open fd. (Also fixes a
second latent bug found during verification: `rt_process_wait`'s timeout
argument is silently ignored by the interpreter backend, always blocking
until real exit — so the fix does not rely on that argument at all.)
`src/app/io/_CliCompile/compile_targets.spl`: `cli_native_build`'s single
`CompileResult.Success` funnel now hard-fails with a loud error if the
output binary doesn't exist on disk, instead of returning 0.
`src/app/cli/native_build_main.spl`: belt-and-suspenders parent-side check —
if the worker exits 0 but the `-o` path is missing, fail loudly instead of
proceeding. Verification = next full stage4 run (see Verification section
below for what was validated locally).

## Symptom

`simple native-build --backend cranelift --source src/compiler --source
src/app --source src/lib --entry-closure --entry src/app/cli/main.spl ...`
(bootstrap stage 4) reproducibly leaves the worker (`simple-main`, running
`src/app/cli/native_build_main.spl`) as a **zombie within seconds**, while
the parent `simple` process blocks forever (0% CPU, ~30 MB RSS, `Sl`);
the stage log contains only the command line + the benign DynamicPath
warning. The bootstrap script then burns its full 7200 s timeout. Observed
twice in a row (2026-07-02 23:09 and 2026-07-03 00:2x); bootstrap stage 2
(same binary, `bootstrap_main.spl` entry) is unaffected.

## Diagnosis

- The parent never reaps the dead child → it is blocked on something other
  than `waitpid` (likely a pipe read that doesn't see EOF, or a missed
  SIGCHLD race).
- Under `strace -f` the timing shifts and the whole chain **exits 0 in
  ~11 s without producing a binary** (worker helper receives a SIGPIPE
  sent via `kill()` from its sibling, then `exit_group(0)`), so the worker
  side also has an early-exit path that reports success with no output.
- Running the worker entry **directly** (`simple run
  src/app/cli/native_build_main.spl -- <same args>`) works: it compiles
  normally (used as the workaround below).

## Workaround (used for the 2026-07-03 redeploy)

Run stage 4 without the worker wrapper:

```sh
src/compiler_rust/target/bootstrap/simple run src/app/cli/native_build_main.spl -- \
  --backend cranelift --source src/compiler --source src/app --source src/lib \
  --entry-closure --entry src/app/cli/main.spl \
  --runtime-path "$PWD/src/compiler_rust/target/bootstrap" \
  -o build/bootstrap/full/x86_64-unknown-linux-gnu/simple
```

then deploy manually per `.claude/rules/bootstrap.md` (cp `.new` + mv, smoke
gates).

## Next steps

- Find the worker-spawn plumbing (parent side of `simple-main`) and make the
  parent robust to early worker death: `waitpid` with the pipe read, treat
  worker exit without output as a hard error immediately.
- Find the worker's silent exit-0 path (SIGPIPE between helper processes)
  and make it fail loudly.

## Verification

- `bin/simple lint` on all three edited files: OK.
- `test/01_unit/app/io/timeout_spec.spl` (and its `test/unit/` mirror)
  exercises `process_run_timeout` directly, including a regression case that
  reproduces the exact bug (a direct child that backgrounds a grandchild and
  exits immediately must not block the parent): `bin/simple test
  test/01_unit/app/io/timeout_spec.spl` — 6/6 pass, ~1.1s total, no hang.
- Full stage4 rebuild was intentionally NOT run here (hours; one already in
  progress elsewhere per instructions) — final confidence still requires the
  next full stage4 bootstrap pass to exercise the actual worker-spawn chain
  end-to-end through a freshly rebuilt self-hosted binary.

## Reopened evidence (2026-07-18)

Two incorrectly routed bootstrap probes were stopped by an outer 900-second
GNU `timeout`, but each interpreted `native_build_main` parent left its nested
`timeout --kill-after=5s 7200s` and worker alive. The two workers were adopted
by PID 1 and retained approximately 1.6 GiB RSS each while their native-build
caches remained empty. All four owned processes required explicit termination.

This does not indicate a native-project cache stall—the probes omitted the
canonical `SIMPLE_NATIVE_BUILD_RUST=1` seed override—but it proves the current
timeout regression covers normal child exit while missing parent interruption.

Required prevention evidence: start `process_run_timeout` with a long-lived
descendant, terminate the Simple parent, and assert within a short deadline that
neither wrapper nor descendant remains. The shared Unix process owner must
propagate parent death or perform equivalent process-group cleanup; extending
timeouts is not a fix.
