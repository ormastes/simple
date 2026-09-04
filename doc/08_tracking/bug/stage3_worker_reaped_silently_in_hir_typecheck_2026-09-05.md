# Stage-3 worker dies silently in phase 3, and it is NOT an OOM

**Status:** OPEN — sole remaining Stage-3 blocker after the ZeroKind and import fixes
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
