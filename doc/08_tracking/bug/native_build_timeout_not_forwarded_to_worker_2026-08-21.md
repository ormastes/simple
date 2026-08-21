# native-build: "worker timed out after 569328s" at 2742 s of wall, and the phase-2 worker outlived the driver (2026-08-21)

**Status:** FIXED (working tree, stage-1 bootstrap lane). Specs:
`test/01_unit/app/cli/native_build_timeout_parse_spec.spl` (7 examples, the
2026-08-09 spec plus the run6 numbers) and
`test/01_unit/app/io/process_run_timeout_live_group_kill_spec.spl` (3 examples).

## Symptom (run6, tree 5020e8f3f45, deployed seed, `--threads 8 --timeout 36000`)

`scratchpad/fp6/stage1_build.log`, last lines (after ~800 lines of
`[hir-payload-origin-unresolved] ...` noise, stderr truncated to 12 KB, full
copy in `/mnt/data/tmp/native-build-stderr-3633308.log`, 171 KB):

```
!!!!!! END NATIVE-BUILD TRUNCATED STDERR !!!!!!error: native-build worker timed out after 569328s before producing a binary.  The interpreted worker loads the whole compiler + LLVM import graph before any  codegen; a large --source set (e.g. src/os + src/lib) exceeds the budget. Raise  --timeout, shrink --source, or use the in-process backend for cross-target builds.
stage1 rc=255 wall=2742s
```

The HIR phase was at 10/667 (+1394 s, ~110-160 s per driver module). The
driver exited at 2742 s; the phase-2 worker (pid 3447260) kept running at
100% CPU for ~25 more minutes until killed by hand.

## Which timeout fired: none

Three separate defects line up to produce that message:

1. **`--timeout` was mis-parsed (known since 2026-08-09, never fixed).**
   `src/app/cli/native_build_main.spl::native_build_parse_secs` accumulated
   `n = n * 10 + int(ch)`, and on the seed interpreter `int("3") == 51` (the
   code point; probe `scratchpad/intprobe.spl`). So `--timeout 36000` became
   `5,1 -> 564 -> 5688 -> 56928 -> 569328` seconds (6.6 days) and `--timeout 1`
   became 49 s. `native_build_timeout_ms` forwards that to the wrapper
   (`timeout --kill-after=10s 569328s ...`), which therefore could not have
   fired at 2742 s. `doc/08_tracking/bug/native_build_worker_timeout_misaccounted_2026-08-09.md`
   had the root cause and a spec, but HEAD still carried `int(ch)` and the
   helpers were private, so the spec could not even import them.

2. **A wrapper that dies by a signal is reported as a timeout.**
   `process_run_timeout_live` returns `-1` both for a genuine `timeout` exit
   (124, with a `[TIMEOUT: ...]` marker appended to stderr) and for
   `rt_process_wait` returning `-1`, which `env_process.rs:1009`
   (`status.code().unwrap_or(-1)`) yields whenever the wrapper was killed by a
   SIGNAL. `native_build_main.spl` then printed the "timed out after {secs}s"
   text for every `-1`. The run6 stderr has **no** `[TIMEOUT:` marker: the
   wrapper (`sh -c "exec timeout ..."`, whose command line contains the
   worker's `native-build ...` arguments) was killed externally, most likely
   by one of the process sweeps of the day that matched on `native-build`.

3. **Killing the wrapper orphaned the real worker.** `timeout` (GNU coreutils
   9.4 here) does not put its command into a process group of its own that
   the driver knows, and the driver only ever signalled the wrapper pid
   (`rt_process_kill` = SIGKILL on the `sh`/`timeout` process), so
   `stdbuf -> simple run native_build_worker.spl` was re-parented to init and
   ran on. Same shape as the 25-minute orphan the coordinator killed by hand.

## Fixes

- `src/app/cli/native_build_main.spl`: digit value is `ch.char_code_at(0) - 48`;
  `native_build_parse_secs` / `native_build_timeout_ms` are `pub`; a `-1`
  without the `[TIMEOUT:` marker is reported as
  `worker wrapper exited abnormally (signal or wait failure, code -1) ...
  its process group has been terminated`, not as a timeout.
- `src/app/io/process_ops.spl` (the copy the driver runs) and
  `src/lib/nogc_sync_mut/io/process_ops.spl` (the copy the spec lane
  resolves `app.io.process_ops` to — verified with a marker file: spec lane
  writes `std`, `bin/simple run` writes `app`): the worker is spawned as
  `exec setsid -w sh -c "echo $$ > <pgid_file>; exec timeout ... stdbuf ... cmd"`
  so the whole tree lives in a fresh SESSION whose id the leader records;
  on every non-zero wrapper result (timeout, relay error, signal death) the
  driver now runs `pkill -TERM -s <sid>` then `pkill -KILL -s <sid>`
  (`_process_kill_group`). Kill by session rather than process group
  because GNU timeout 9.4 moves its command into a new group
  (`ps` during the probe: sh pgid 3986544 != sid 3986452), so a group kill on
  the leader pid misses the worker. `setsid -w` keeps the wrapper pid alive
  with the tree's exit status whether setsid forks or execs in place.
- Level-gated receipt: `SIMPLE_PROC_DEBUG=1` prints
  `[proc-debug] kill-group pgid=<sid> term_code=.. kill_code=..`.

## Evidence

- Parse: `int("3")` probe = 51; `"36000"` accumulates to 569328 (matches the
  log). Spec before the fix could not import the private helpers; after:
  7/7.
- Orphan: `scratchpad/tmo/probe5.spl` (`sh -c "kill -KILL $PPID; sleep 37.0731"`,
  i.e. the worker kills its own wrapper): before, `survivors=[<sleep pid>]`;
  after, `survivors=[]` in both JIT and interpret mode. Spec example 3
  (`sleep 37.0731 & exit 3`): before `expected 2 to equal 0`; after 3/3.
- A 2 s worker under a 60 s budget returns 0 with no marker; a 3 s worker
  under a 1 s budget returns -1 with `[TIMEOUT: Process killed after 1s]`.

## Not changed

`rt_process_wait`'s `-1` for signal deaths (`env_process.rs`) is a seed
change and belongs to the seed lane; the driver now classifies it correctly
instead of blaming `--timeout`.
