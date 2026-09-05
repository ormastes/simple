# native-build worker leaks unboundedly in the seed interpreter's execution phase

- **Filed:** 2026-08-17 (lane LEAK)
- **Severity:** P1 — host-wide. Causes earlyoom kills of every `native-build`
  worker on this box, which blocks the mandatory pre-push guard
  `check-native-extern-fabrication.shs`.
- **Component:** Rust bootstrap **seed** interpreter
  (`bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`), exercised via
  `src/app/cli/native_build_worker.spl`.
- **NOT the same defect as**
  `native_build_worker_timeout_blocks_all_pushes_2026-08-17.md` (owned by another
  lane). That row is about the GUARD symptom; this row is the underlying
  unbounded memory growth. Do not merge them.

## Reproducer (2 lines of input, 1 source file)

```bash
S=/tmp/leakrepro; mkdir -p $S
printf 'fn main() -> i64:\n    0\n' > $S/tiny.spl
SIMPLE_NATIVE_BUILD_WORKER=1 bin/simple run src/app/cli/native_build_worker.spl \
    --entry $S/tiny.spl -o $S/tiny.out > $S/run.log 2>&1 &
P=$!    # poll the `simple` child, not the shell
while [ -r /proc/$P/status ]; do
  awk '/^VmRSS/{print $2}' /proc/$P/status
  awk '{print $14"/"$15}' /proc/$P/stat      # utime/stime
  wc -l < $S/run.log                          # log progress
  sleep 20
done
```

## Measured, independently, on 2026-08-17 (this lane, PID 1615953)

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, which prints
`WARNING: this Rust-built Simple binary is a bootstrap seed only`. **Seed.**

| t | RSS | utime/stime | stdout log lines |
|---|---|---|---|
| 30s | 176 MB | 101/447 | (loading) |
| 20s* | 492 MB | 330/1428 | 671 |
| 40s | 363 MB | 553/1940 | 1115 |
| 60s | 693 MB | 732/2531 | **1335** |
| 80s | 1125 MB | 1062/2972 | 1335 |
| 100s | 1395 MB | 1312/3230 | 1335 |
| 120s | 1996 MB | 1855/3489 | 1338 |
| 140s | 2249 MB | 2105/3683 | 1338 |
| 160s | 2704 MB | 2519/4159 | 1342 |
| 180s | 2875 MB | 3035/4397 | 1349 |

Monotonic throughout, no plateau, never `D` state. Run terminated by this lane
at t=180s (own PID only). Growth in phase B: 693 MB -> 2875 MB in 120s.

(\* two pollers with different epochs; the second column is the one that matters.)

`smaps_rollup` at ~365 MB: `Anonymous: 351032 kB`, `Private_Dirty: 351032 kB`,
`Pss_File: 469 kB`, 28 `rw-p` mappings. **All growth is private anonymous heap.**
Not mmap'd source files, not page cache, not shared.

## WHAT grows, and in which phase — the phase split is the finding

The run has two clearly separable phases, and they are separable *because log
output plateaus while RSS does not*:

- **Phase A, t=0..60s — module load / parse / lint of the whole compiler graph.**
  stdout climbs 0 -> 1335 lines (all of them lint warnings against
  `src/compiler/**`, `src/lib/**` — files `tiny.spl` never imports). RSS 176 ->
  693 MB. **stime dominates** (447 -> 2531): this is file I/O and page-in.
- **Phase B, t=60s onward — interpreted execution of the compiler pipeline.**
  Log output **stops dead at 1335 lines and never moves again**. RSS keeps
  climbing 693 -> 1996 MB in 60s, i.e. **~22 MB/s**, and now **utime dominates**
  (732 -> 1855, accelerating) while stime growth flattens. Never in `D` state.

That rules out three of the four candidate causes by direct evidence:

- **Not output buffering** — zero bytes are produced during the growth phase.
- **Not repeated re-parsing / re-lint** — the lint pass is finished and its
  output is quiescent before growth accelerates.
- **Not the import/module graph being re-materialised** — that *is* phase A, and
  phase A plateaus.

What remains, and what the code supports: **values allocated by the interpreted
program during execution are never reclaimed.** The seed has **no garbage
collector at all** — `grep -rln 'collect_garbage|garbage_collect|mark_and_sweep|struct Gc\b'`
over `src/compiler_rust` (excluding vendor) returns **zero files**. Reclamation
in `src/compiler_rust/runtime/src/value/heap.rs` is explicit-only: every
allocation is `register_heap_ptr`'d into a process-global
`HEAP_ALLOCATION_REGISTRY: Mutex<HashSet<usize>>` and leaves it only via an
explicit `unregister_heap_ptr*` call from a hand-written destructor site. The
in-source name for the contract is literally
`rt_core_unregister_immortal_ptr` — heap objects are **immortal by default**.
Under `src/compiler_rust/compiler/src/interpreter_extern/` the single
`unregister_heap_ptr` occurrence is inside a `#[test]` function
(`mod.rs:2943`), so the interpreter's non-test path frees nothing.

**Honest limit on the attribution:** this identifies an
unbounded-by-construction mechanism and the phase in which the growth happens.
It does not prove which allocation site dominates the 22 MB/s. Confirming that
needs an allocator profile, and **attach-based profiling is unavailable on this
host**: `kernel.yama.ptrace_scope = 1`, `kernel.perf_event_paranoid = 4`. A
heaptrack/dhat-instrumented seed build would settle it, but rebuilding
`bin/simple` clobbers ~15 concurrent lanes and was deliberately not done.

## Why input size is irrelevant

The 1335 lint warnings are the proof. `native_build_worker.spl` is a 27-line
shim that imports `app.io._CliCompile.compile_targets.{cli_native_build}`, which
transitively pulls in the entire compiler + LLVM backend graph. The seed
interpreter must load, parse, lower and then *interpret* that whole graph before
it looks at the user's entry file. A 2-line hello-world and a 2-file `--source`
therefore cost exactly what the whole tree costs. This is consistent with the
reported table (4.77 GB at t=0 rising to 6.22 GB at 8m47s) — that run was simply
observed later in phase B, at a slower rate under heavy host contention.

## Is this fixable in `.spl`?

**No — not in the files this lane owns, and a `.spl` change here would be a
half-fix of an allocator problem.**

- `src/app/cli/native_build_worker.spl` is 27 lines of argument slicing and an
  env guard. There is nothing in it to leak.
- `cli_native_build` (`src/app/io/_CliCompile/compile_targets.spl:688`) begins
  with pure argument parsing over a short `[text]`; the growth phase is far
  downstream of it.
- The defect is that the seed runtime has no reclamation mechanism for
  interpreted values. That cannot be repaired from Simple source. Adding
  `.spl`-level "free" calls or restructuring loops would at best move the
  constant and would misrepresent an allocator gap as an application bug.

**The architecture is the real defect:** a worker should not interpret the entire
compiler + LLVM graph in a GC-less interpreter in order to build a 2-line
program. The strategic fix already exists and needs no code change:

```bash
SIMPLE_NATIVE_BUILD_RUST=1   # dispatch at src/compiler_rust/driver/src/main.rs:168-178
```

routes the build **in-process** through the Rust driver instead of spawning an
interpreted worker. Reported measurement: **RC=0 in 50s with flat memory**. That
is the recommended route for anything that needs to SUCCEED, including the
pre-push guard, until either (a) a reclamation strategy lands in the seed, or
(b) the worker stops being an interpreted whole-compiler process.

## Consequence: rc=255 was OOM, not the timeout

`native-build`'s own timer prints `[TIMEOUT: Process killed after Ns]`. That line
was **never emitted** in the failing guard runs. Its absence is the discriminator:
those were earlyoom SIGKILLs (earlyoom runs here with
`--prefer ^(simple|rustc|...)`), not the worker's timeout. Any future rc=255 /
rc=137 on this path must be classified with that same test before being called a
timeout. rc=143/144 remains UNVERIFIED and must not be reported as "failed".

## Live workers on this host

At the time of filing, `pgrep -cf native_build_worker` reported **30**, each in
phase B and each climbing on the order of a GB per few minutes, against ~4 GB
free of 125 GB. They are the direct cause of the host's memory pressure and of
earlyoom's kill activity.

**Recommendation — do NOT mass-kill.** A lane used a broad `pkill -f` earlier
today and destroyed other lanes' processes. Correct procedure:

1. Each lane reaps **only the PIDs it personally started**, by explicit PID.
2. New invocations set `SIMPLE_NATIVE_BUILD_RUST=1`; the interpreted worker is
   used only for deliberate, short, polled leak measurement.
3. `scripts/check/check-native-extern-fabrication.shs` should be routed through
   the in-process path (owned by the scripts lane — not changed here).

This lane started exactly one worker (PID 1615953) and killed exactly that one.
