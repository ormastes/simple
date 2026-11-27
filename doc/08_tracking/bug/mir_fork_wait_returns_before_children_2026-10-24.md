# MIR fork root "reaps" children instantly; children SIGKILLed (2026-10-24)

**Symptom (Phase-3 run-18, SIMPLE_MIR_FORK_WORKERS=20):** every
`[mir-fork] child owner=0/1@0+forkK/20 exit=-1 sealed=0 finished=false`, then
`unclaimed=-1`, `root done ... failed=true`, `inventory incomplete rows=-1`,
coordinator fallback to in-process unsharded MIR. No child printed
`[mir-shard] done`; one child `[mir-lower] WARNING` is interleaved between the
fork17 and fork18 reap lines (log line 108678): children were alive and had
started `lower_to_mir` when they died.

**Root cause:** the root reaped with `process_wait_raw` -> `rt_process_wait`.
The producer links the Rust runtime lane's `rt_process_wait`
(`src/compiler_rust/runtime/src/value/sffi/env_process.rs:1272`; disassembly
of the producer at 0x2043730 calls `SPAWNED_CHILDREN` / `Child::try_wait`),
which only knows pids in its own spawn registry and returns `-1` at once for
any other pid, without calling `waitpid`. A `rt_fork_shared_heap_v1` child is
never registered, so all 20 "waits" returned immediately. The root then read an
inventory that no child had published yet (`unclaimed=-1`), re-forked nothing,
completed and exited; `PR_SET_PDEATHSIG(SIGKILL)` (`runtime_fork.c`) killed
every child. Fork ordering (before `lower_to_mir`) is by design: each child
lowers and publishes like a spawned shard worker.

**Fix:** `rt_fork_shared_heap_wait_v1(pid)` in `src/runtime/runtime_fork.c`,
next to the fork primitive (always linked with it): blocking `waitpid` with
EINTR retry, exit status / `-(128+signo)` / `-1`. Wrapper
`fork_shared_heap_wait_v1` in `src/lib/nogc_sync_mut/sffi/process.spl`, used at
`native_mir_fork_v1.spl:157`. Needs a runtime-capsule rebuild to take effect.

**Probe:** `build/repro/fork_wait_probe.c` linked with `runtime_fork.c` and the
p2shard-11 capsule's `libsimple_native_all.a`:
`rt_process_wait(forked pid, 0) = -1 (child still alive: yes)`; new wait = 7;
SIGKILLed child = -137; non-child pid = -1.
