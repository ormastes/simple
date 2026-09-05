# Stage-3 worker dies silently in phase 3, and it is NOT an OOM

**Status:** OPEN — sole remaining Stage-3 blocker after the ZeroKind and import fixes
**READ `## UPDATE 2` FIRST.** The cause is a **SIGSEGV** in the Stage-2 compiler.
The title and the two sections below it record two earlier readings that are
both wrong (a kill, then an `exit(-1)`); they are kept only as history.
**Filed:** 2026-09-05
**Host:** aarch64-unknown-linux-gnu, 20 cores, 121 GB

## Symptom

```
warning: stage3 self-host worker was KILLED (reaped without a normal exit;
  the signal number was discarded by an older runtime ...); NOT a compile failure
error: --stop-after-stage3 requires a successful Stage 3 compiler
```

The worker dies between 1h and 1h45m of single-core work, always inside
`phase3:hir_typecheck`, and leaves **no diagnostic of any kind** — the saved
worker stderr ends mid-trace with zero `error`, zero `abort`, zero allocation
message.

## What has been ruled out, with evidence

| hypothesis | evidence against |
|---|---|
| compile error | 0 `HIR lowering error`, 0 `E-MIR-TYPE-ZeroKind`, 0 `post-mono-verify` in the worker stderr |
| worker timeout | budget is 6h (`DEFAULT_TIMEOUT_MS` raised 2026-09-04); deaths occur at ~1h-1h45m, and the live wrapper was confirmed as `timeout --kill-after=10s 21600s` |
| kernel OOM | no `Killed process` / `Out of memory: Kill` in `dmesg -T` |
| cgroup OOM | `/sys/fs/cgroup/<slice>/memory.events` reports **`oom_kill 0`**, and `memory.max` / `memory.high` are both `max` |
| host memory pressure | tree RSS 48-50 GB with 121 GB total; the run that died at 1h42m was EXCLUSIVE (116 GB free at start, nothing else building) |
| contention with a second build | reproduced with the machine to itself |
| the `bcmp`/libc stub defect | fixed and verified earlier; Stage 2 links `U bcmp` and its build reports only 1 compatibility alias |

## Why the signal number is still missing

`rt_process_wait`'s WNOHANG path already returns `-(128+signo)` on
`WIFSIGNALED`, and 2026-09-05 the same treatment was added to its blocking path
(`src/runtime/runtime_process.c`). The runtime archive that Stage 2 links was
rebuilt AFTER that edit (archive 05:33 vs source 05:12), so the fix is present —
yet the caller still sees the bare `-1` that renders as 255.

That leaves one reading: neither `WIFEXITED` nor `WIFSIGNALED` was true, i.e.
**`waitpid` itself failed** and returned < 0. The likely cause is `ECHILD` — the
child was already reaped by someone else. `process_run_timeout_live`
(`src/lib/nogc_sync_mut/io/process_ops.spl:284`) spawns through `setsid` and
polls with its own budget, so a second reaper in that path would produce exactly
this: a process that is gone, a wait that fails, and no signal to report.

## Next steps, in order

1. Instrument `rt_process_wait`'s `waitpid(...) < 0` branch to report `errno`
   (distinguish `ECHILD` from `EINTR`). This is the cheapest possible probe and
   settles whether the child is being double-reaped rather than signalled. Note
   `check-process-wait-eintr-retry` already exists as an advisory push gate —
   the EINTR path has a history here.
2. If `ECHILD`: find the second reaper on the `process_run_timeout_live` path.
   The worker may in fact have exited normally, with its status lost — in which
   case Stage 3 may be much closer to green than the "KILLED" wording suggests.
3. Only if that is excluded, treat it as a genuine crash in the Stage-2
   compiler during `hir_typecheck` and bisect by module.

## Context

This is the last blocker on a Stage-3 self-host for this host. Everything ahead
of it is fixed and verified: the `Optional<aggregate>` codegen defect that
caused `E-MIR-TYPE-ZeroKind` (3 raises -> 0), the 57 fabricated libc stubs
including `bcmp`, and the HIR import-resolution failure in
`driver_compile_vhdl_expr.spl`. Phase 3 now completes on some runs and the build
has reached `phase4:monomorphize:done` and `aot:lower_to_mir:start`.

## UPDATE: waitpid did NOT fail — 255 is the worker's own exit(-1)

The errno probe added to `rt_process_wait`'s `waitpid(...) < 0` branch
(`diag(runtime): say why waitpid failed instead of collapsing it to -1`) printed
**nothing** across a full Stage-3 run that ended in the same "KILLED" message.
So that branch was never taken: `waitpid` succeeded.

That eliminates the ECHILD / double-reap theory from the section above, and with
`WIFEXITED` false ruled out too (the caller would have seen the real code), the
remaining reading is the one the older record already named:

> 255 ... is the conventional shell rendering of an exit(-1)
> — `doc/08_tracking/bug/bootstrap_exit_255_misreported_as_signal_127_2026-09-02.md`

**The worker is not being killed at all. It is exiting -1 on one of its own
error paths, silently, during `phase3:hir_typecheck`.** The bootstrap's
"was KILLED (reaped without a normal exit)" wording is therefore actively
misleading here and has now cost three separate investigations — an OOM hunt, a
rogue-killer hunt, and a double-reap hunt — all excluded by measurement.

### Corrected next steps

1. Fix the classification in `bootstrap-from-scratch.sh` (~:2937): a 255 must not
   be reported as "KILLED ... signal number discarded". Per the 2026-09-02
   record it is an `exit(-1)`. The runtime now reports genuine signal deaths as
   `-(128+signo)`, so that arm can say so plainly.
2. Find the worker's `exit(-1)` / `return -1` path that runs during HIR
   typecheck and give it a message. It currently produces no stderr whatsoever —
   the saved worker log ends mid-trace with zero `error` lines.
3. Only then resume bisecting the Stage-3 build itself.

Everything ahead of this in the pipeline is fixed and verified; see the Context
section above.

## UPDATE 2 (2026-09-05, afternoon): it is a SIGSEGV. Both earlier readings were wrong.

The evidence was already on disk when UPDATE 1 was written, in two places
nobody had looked:

```
build/bootstrap/logs/aarch64-unknown-linux-gnu/stage3-native-build.log:23649
    timeout: the monitored command dumped core

/var/log/apport.log
    2026-09-05 08:04:07,490: called for global pid 1387485, signal 11, core limit 0, dump mode 1
    executable: .../stage3/aarch64-unknown-linux-gnu/stage2-admitted/simple
      (command line ".../stage2-admitted/simple run src/app/cli/native_build_worker.spl
       --target aarch64-unknown-linux-gnu --backend llvm --runtime-bundle core-c-bootstrap
       --threads 2 ... -o .../simple src/app/cli/bootstrap_main.spl")
    executable does not belong to a package, ignoring
```

**Signal 11 = SIGSEGV, in the Stage-2 compiler, running the Stage-3
native-build worker.** It is not an OOM, not an external kill, not a double
reap, and not an `exit(-1)` on one of the worker's own error paths. UPDATE 1's
retraction of the signal reading is itself retracted; the 2026-09-03
"CORRECTED" note in the bootstrap's 255 arm was closer to the truth than what
replaced it.

### Why four investigations missed a line that was sitting in the log

1. `timeout`'s `dumped core` line was not in `native_build_line_is_diagnostic`,
   so `eprint_bounded` dropped it with the other 9,929,264 of 9,941,264 stderr
   bytes it drops **from the middle**. It survived here only because the crash
   happened close enough to the end to land in the preserved tail.
2. The 255 never meant "killed". It is `native_build_main.spl` returning its own
   `-1` from `process_run_timeout_live`. **Which `-1`, and from which of the two
   `rt_process_wait` twins, is NOT yet established** — and the fix below does
   not depend on the answer, because it keys on the `dumped core` string rather
   than on the number.
   What is known: `runtime_process.c` reports `-(128+signo)` on `WIFSIGNALED`
   since 2026-09-05, while both **Rust** twins still end
   `status.code().unwrap_or(-1)`
   (`src/compiler_rust/runtime/src/value/sffi/env_process.rs:1002,1021`,
   `compiler/src/interpreter_extern/system.rs:1226,1241`) and `ExitStatus::code()`
   is `None` for a signal death — so WTERMSIG is discarded there exactly as it
   used to be in C. That is a real gap either way.
   What does NOT add up, and is left open rather than papered over: the polled
   pid is the outer `/bin/sh` that execs `setsid -w`, and `setsid -w` exits
   *normally* with `128+signo` when its child dies by a signal, so a correct
   wait should have returned **139**, not `-1` and not `None`. Candidates still
   to check: `setsid` exec'ing in place instead of forking (so the polled pid is
   itself the SIGSEGV victim), or the Rust twins' "pid not found in
   SPAWNED_CHILDREN" arm, which also returns a bare `-1`. The errno probe added
   to the C function printing nothing is consistent with the C function never
   running, but does not prove it.

### Fixed in this change (diagnostics only — the SEGV itself is still open)

- `native_build_line_is_diagnostic` now keeps `dumped core` / `core dumped`, so
  the line can never again be truncated away.
- `native_build_main.spl` classifies a `-1` whose stderr carries `dumped core`
  as **CRASHED**, and prints the apport/gdb recipe for a backtrace.
- The bootstrap's 255 arm no longer asserts a kill; it says the wrapper lost the
  status and points at the log that carries the real classification.

### Core dumps now get saved on this host

apport was receiving the core and discarding it (`executable does not belong to
a package, ignoring`). Fixed without root:

```sh
printf '[main]\nunpackaged=true\n' > ~/.config/apport/settings
```

Verified with a deliberate SIGSEGV: apport wrote `/var/crash/<path>.crash` plus
a core under `/var/lib/apport/coredump`. `core_pattern` is a pipe, so
`RLIMIT_CORE=0` does not suppress it. The next Stage-3 run therefore yields a
backtrace:

```sh
apport-unpack /var/crash/<report>.crash /tmp/u
gdb <stage2-admitted/simple> /tmp/u/CoreDump -batch -ex bt
```

### Remaining next steps

1. Re-run Stage 3 and take the backtrace. **This supersedes the module bisect**
   in the previous section — do not bisect before reading the trace.
2. Port the signal fix to the Rust twins named above so `-(128+signo)` survives
   there too (`rt_*` dual-implementation gap; the C half is already done). Note
   `native_build_main.spl` currently only normalises the zero-extended
   `4294967295` back to `-1`, so a `-139` would surface as `4294967157` — that
   normalisation has to be widened in the same change.
3. Lead, not a hypothesis: the last file before the crash,
   `src/compiler/driver/pipeline_fn.spl`, chased the builtins `Option` / `text`
   / `i64` as re-exports through `compiler.common._Attributes.decl_attrs` and
   registered nothing. A nil-aggregate deref in native code is the same class as
   the `E-MIR-TYPE-ZeroKind` defect fixed on 2026-09-03. The worker also runs
   `--threads 2`, and the death point varies (1h–1h45m), which fits a race or a
   use-after-free better than deterministic recursion. `--threads 1` is the
   one-run discriminator if the backtrace proves unobtainable.

### Two collateral defects found while fixing the diagnostic (both fixed here)

1. **The streaming diagnostic collector had been clobbered by a merge.**
   `5975608cddc perf(native-build): stream sparse diagnostics` replaced the
   `for line in output.split("\n")` collector — which materialises the whole
   9.9 MB stream as an array of lines — with a `native_build_range_contains`
   scanner that never allocates. `e274cd33719 chore: merge all share-history
   worktree branches into main` reverted the implementation and kept the test.
   Restored, with the two new needles folded in. This is the sync-clobber
   pattern `.claude/rules/vcs.md` § "Sync must never clobber" describes.
   Bounded, so the restore is known to be complete: comparing the top-level
   function sets of the file at `5975608cddc` and at `HEAD`, the ONLY names
   present then and missing now were `native_build_range_contains` and
   `native_build_range_is_diagnostic` (`run_native_build_worker` merely gained
   `pub`). Nothing else in this file was reverted.
2. **The test that should have caught (1) had never run.** It ends
   `expect(src).not_to_contain(...)`, and `not_to_contain` is not a matcher this
   spec runtime has — `src/lib/nogc_sync_mut/spec.spl` offers `to_contain` plus
   an `ExpectScalarMatcher.not_()` that is implemented for `i64` only (and used
   by zero tests). So the example ERRORED on every run with `method
   not_to_contain not found on type str` and the guard was decorative. Rewritten
   as `expect(src.contains(...)).to_be_false()`.
   Open feature request, not fixed here: a `not_()` (or `not_to_*`) negation
   usable on `text`, and a spec-runtime rule that an unknown matcher is a hard
   error at the file level rather than one silently red example among ten.

`test/01_unit/app/cli/native_build_bootstrap_lane_contract_spec.spl` is now
10/10 green, up from 9/10 with the guard permanently broken.
