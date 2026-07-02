# native-build parent hangs forever when its worker dies early (zombie, empty log)

Date: 2026-07-03
Status: open
Severity: P1 (blocks bootstrap stage 4 / --deploy on this host; silent 2h timeout burns)
Found by: fable orchestrator during bootstrap redeploy

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
