# A failed bootstrap leaves orphan workers running and its output lock held

- **Filed:** 2026-09-06
- **Status:** OPEN
- **Severity:** P1 — one failed bootstrap blocks every later bootstrap on the
  host, with an error that names the wrong problem, while leaking tens of GB.
- **Component:** `scripts/bootstrap/bootstrap-from-scratch.sh` failure path
  (`portable_lock_acquire` at :750, `bootstrap_lock_handle`)

## What happened

A Stage 3/4 run failed at 13:16:37 and the wrapper exited `rc=1`. Its process
tree did **not** exit: the run's shell (pid 619228, `ppid 1`, `Ss`) was still
alive 19 minutes later with a child chain ending in a `simple` worker (pid
646117) at **42,392,196 KB RSS (42.4 GB)**, state `R`, 17 minutes of CPU.

That orphan still held the output-ownership lock
`build/.simple-bootstrap-locks/.output-<digest>.lock`
(`format=portable-hardlink-lock-v2`, `owner_pid=619228`, alive per `kill -0`).

So the next bootstrap died 60 seconds in with:

```
error: timed out waiting for bootstrap output ownership: /home/yoon/bootstrap-wt/build/bootstrap
failure_root=stage2   failure_reason=stage-engine-failed
```

`failure_root=stage2` is wrong and cost real debugging time: Stage 2 was never
reached. The lock wait (`SIMPLE_BOOTSTRAP_LOCK_WAIT_SECONDS`, default 30) is
the whole story, and the manifest attributes it to the first stage in the graph.

Killing the process group (`kill -KILL -619228`) released the lock and returned
42 GB; the next run started normally.

## Two defects, and neither is the lock design

1. **The failure path does not reap the run's own workers.** The wrapper exits
   while its process group keeps running. The lock is correctly released only
   on a clean exit, so a crash or a hard stage failure strands it — held by a
   process nobody is waiting on, that no longer has a supervisor, and that goes
   on consuming memory. `-KILL` on the group was the only remedy available.
2. **The failure manifest attributes a pre-stage failure to a stage.** Anything
   that fails before the stage engine starts — lock timeout, disk floor, an
   admission refusal — should say so, not report `failure_root=stage2`.

## Related, not the same

The 42.4 GB single worker is its own defect: per-worker footprint, not worker
count. `native_build_worker_interpreter_heap_grows_unbounded_2026-08-17.md`
carries the measured plateau (~3.2 GB interpreter lane) and the JIT-lane leak
(110,758,831 allocations, 0 frees); 42 GB is far above the interpreter plateau
and was still growing, so it belongs with the JIT-lane row there.
`50d50594fc5` bounds the worker *count* by available memory; it does nothing
about one worker growing without bound, and does not address this bug at all.

## Repair sketch (not implemented)

- Trap the failure exits and `kill` the run's own process group before
  releasing the lock, so the lock and the workers die together.
- Record a distinct `failure_root=pre-stage` (or the specific gate) whenever
  the failure precedes stage-engine entry.
- Consider a liveness probe in `portable_lock_acquire`: a lock whose
  `owner_pid` is gone, or whose `owner_start_hex` no longer matches that pid's
  start time, is stale and may be broken rather than waited on.
