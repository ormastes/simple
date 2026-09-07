# native-build worker leaks unboundedly in the seed interpreter's execution phase

> **CORRECTED 2026-09-06 — read the addendum at the bottom before acting on
> anything below it.** The attribution in this record ("values allocated by the
> interpreted program are never reclaimed"; the `HEAP_ALLOCATION_REGISTRY` /
> `rt_core_unregister_immortal_ptr` mechanism) is **wrong for the interpreter
> lane** and **right for the compiled/JIT lane**, which this record never
> examined. Measured directly with an instrumented seed: the whole-compiler-graph
> worker run registers **374 runtime-heap objects / 13 KB** against **3.25 GB
> RSS** — five orders of magnitude off. The 22 MB/s phase-B growth also no longer
> reproduces; that was fixed by `e73a0bec647` (2026-08-21). What remains, and what
> actually caused the 2026-09-06 host OOM, is a **bounded 3.25 GB plateau** during
> module load. Details, tables and the surviving claims: § Addendum.

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

---

## Addendum 2026-09-06 — measured with an instrumented seed; the attribution above is wrong for the interpreter lane

**Method.** The 2026-08-17 investigation stopped at "attach-based profiling is
unavailable and rebuilding `bin/simple` clobbers ~15 lanes". Both are true and
neither blocks the measurement: a seed built into a **private**
`CARGO_TARGET_DIR` and run by absolute path touches no deployed binary. Build:
`cd src/compiler_rust && CARGO_TARGET_DIR=$HOME/.cargo-target-memfix cargo build
--release --bin simple -j6`; binary sha256 `d3be122e16a44cac...`, tree `ef8b58f3dab`,
host aarch64 Linux, 20 CPUs, 121 GB. Instrumentation was a temporary sampler
thread printing `VmRSS`, `mem_trace::live()`, `rt_heap_registry_count()`,
`rt_heap_live_bytes()`, `rt_heap_aux_live_bytes()`, `rt_heap_alloc_count()` and
`rt_heap_free_count()` every 1-5 s. It has been removed; the retained artefacts
are this addendum and the regression test named at the end. The pre-existing
`SIMPLE_MEM_TRACE=1` / `SIMPLE_CACHE_SIZE_REPORT=<n>` reports supplied the
per-module and per-cache attribution and needed no new code.

### The finding: there are two lanes, and this record conflated them

| | interpreter lane (`run`, `lint`, `native_build_worker`) | compiled / JIT lane (a user program the JIT accepts) |
|---|---|---|
| value representation | Rust `Value` enum -- `Arc`/`Vec`/`String` (`compiler/src/value.rs`) | `RuntimeValue` heap objects (`runtime/src/value/heap.rs`) |
| enters `HEAP_ALLOCATION_REGISTRY` | **no** (374 objects / 13 KB observed) | **yes** (110,758,831 objects in 75 s) |
| ever freed | yes, on scope exit (Rust drop) | **never** -- `rt_heap_free_count() == 0` throughout |
| growth | **bounded**, plateaus | **unbounded**, ~80 MB/s |

The mechanism this record describes -- immortal-by-default registration, freed
only by a hand-written destructor call -- is **real and unrefuted**, but it lives
in the lane this record never ran.

### Interpreter lane: bounded, and the registry is irrelevant

Reproducer exactly as filed (2-line `tiny.spl` through
`src/app/cli/native_build_worker.spl`), with and without `SIMPLE_BOOTSTRAP=1`
(the original run set neither; both were tried, with no material difference):

| t | RSS | Rust live | `rt_registry` | `rt_live_bytes` | `rt_frees` |
|---|---|---|---|---|---|
| 0 s | 11 MB | 0 MB | 0 | 0 | 0 |
| 5 s | 1264 MB | 1150 MB | 0 | 0 | 0 |
| 10 s | 2905 MB | 2500 MB | 0 | 0 | 0 |
| 15 s | 3256 MB | 2791 MB | 374 | 13,052 | 1 |
| 20 s | 3256 MB | 2791 MB | 374 | 13,052 | 1 |
| 25 s | 3256 MB | 2791 MB | 374 | 13,052 | 1 |

**The registry accounts for 13 kilobytes of a 3.25 gigabyte process.** RSS
tracks `mem_trace::live()` -- the Rust allocator -- not the runtime value heap.

**Phase B does not grow.** The run reaches the end of the pipeline in ~15-30 s
and RSS is flat from t=15 s. `bin/simple lint src/lib/common/base_encoding.spl`
completes in under 5 s, also flat.

**Confirmed on the DEPLOYED binary too, not just the instrumented build.** The
same reproducer against `bin/release/aarch64-unknown-linux-gnu/simple`
(read-only, `/proc` polling, nothing written to `bin/`) gives
`t=0s 4.6 MB, t=10s 2.54 GB, t=20s exited` -- same shape, same bounded plateau.
This matters because a fresh mtime on a deployed seed is exactly what a stale
copy looks like (`.claude/rules/bootstrap.md`), so the plateau claim below is
not resting on a binary that only this lane built.

The 22 MB/s climb reported for 2026-08-17 is **not reproducible on a seed
containing `e73a0bec647` "perf(seed): scope-chain CowEnv replaces per-call env
clone" (2026-08-21)**, whose own commit message records the same symptom class
("lint driver_types 90 s/2 GB -> ~24 s/0.5 GB"), and `SIMPLE_MEM_TRACE=1` now
reports `captured_env_with_live_globals: calls=0`, i.e. the O(globals)-per-call
path this record was measuring is dead code. That is correlation plus a dead
code path, not a bisect: no pre-fix seed was built and run.

**`rc=1` on this reproducer is `ld.lld: error: unable to find library -lSDL2`,
not OOM and not the leak.** Do not read a non-zero exit here as the defect.

### What the 3.25 GB actually is, and why it OOM'd the host

`SIMPLE_MEM_TRACE=1` at process exit, for a 2-line input:

```
module_loads=738  source=12.7MB  ast_items=18883
parse_retained=453.9MB  eval_retained=1405.6MB  parse_bytes_per_source_byte=35.7
env_entries=1357503  export_entries=1348600
globals census: owners=257 module_envs=743 import_bindings=1330952
  (shallow bytes: module_envs 139.7MB, import_bindings 131.5MB)
live=2224.3MB  peak=2797.7MB  rss=3250.7MB
```

12.7 MB of source becomes 3.25 GB of RSS -- a **256x** blowup -- because the
worker interprets the whole compiler + LLVM graph before looking at the entry
file (this record's "why input size is irrelevant" section is correct and
unchanged). Per-module env width grows with the graph: `driver_pipeline.spl` is
237 bytes of source with 4 items and carries an env of **10,239** entries.

**This plateau, not runaway growth, is the 2026-09-06 OOM.** 128 concurrent
processes x ~3.2 GB against 121 GB of RAM is the arithmetic, and the "largest
3.5 GB anon-rss" in that incident is this plateau, not a process caught
mid-climb. Attribution is diffuse -- parse 454 MB, module envs 140 MB, import
bindings 132 MB, exports ~140 MB, with ~1.1 GB unattributed and **no single
structure above 30%** -- so there is no small diff here. Reducing it is a real P1
and a *different* bug from the one filed; the levers are the per-module
env/export materialisation and the fact that a 2-line build loads 738 modules at
all. `SIMPLE_NATIVE_BUILD_RUST=1` remains the correct route for anything that
must succeed today.

### Compiled / JIT lane: this IS unbounded, and the mechanism is exactly as filed

Reproducer -- a loop whose live working set is 40 elements, run through the JIT:

```simple
fn build(n: i64) -> i64:
    var a = []
    var i = 0
    while i < n:
        a.push("item-" + i.to_text())
        i = i + 1
    var d = {}
    var j = 0
    while j < n:
        d["k" + j.to_text()] = a[j]
        j = j + 1
    a.len() + d.len()

fn main() -> i64:
    var total = 0
    var r = 0
    while r < 200000:
        total = total + build(200)
        r = r + 1
    print(total)
    0
```

| t | RSS | Rust live | `rt_registry` | `rt_live_bytes` | `rt_aux_bytes` | `rt_frees` |
|---|---|---|---|---|---|---|
| 0 s | 8 MB | 0 MB | 0 | 0 | 0 | **0** |
| 15 s | 1517 MB | 1374 MB | 27,580,947 | 773 MB | 361 MB | **0** |
| 30 s | 2949 MB | 2701 MB | 54,091,938 | 1517 MB | 708 MB | **0** |
| 45 s | 4429 MB | 4101 MB | 75,094,732 | 2105 MB | 983 MB | **0** |
| 60 s | 5213 MB | 4815 MB | 93,302,152 | 2616 MB | 1222 MB | **0** |
| 75 s | 5967 MB | 5500 MB | 110,758,831 | 3105 MB | 1450 MB | **0** |

Monotonic, no plateau, **not one object freed in 110 million allocations**. Of
the 5.5 GB live: ~3.1 GB object headers, ~1.45 GB container backing, and ~1.1 GB
is the `HashSet<usize>` registry itself (~10 bytes/object of pure bookkeeping on
top of a leak).

**No small fix exists for this, and one was not invented.** `HeapHeader` carries
`gc_color`/`mark_gray`/`mark_black`/`pin` but there is no collector and no
refcount field. The runtime *does* have a working reclamation mechanism --
`rt_transient_array_scope_begin`/`_end` with `rt_transient_heap_promote`
(`runtime/src/value/collections.rs`), used by `src/app/check/main.spl::check_one`
for its per-file scope -- and codegen registers `rt_array_free`, `rt_string_free`
and the transient-scope entry points in its SFFI spec table
(`compiler/src/codegen/runtime_sffi.rs`). **Codegen emits none of them
automatically**: reclamation was never wired, not disabled. Wiring a transient
scope per JIT frame is unsound without escape analysis -- anything stored into a
global, a capture, an outer container, or retained by a callee would be freed
while reachable. Closing this needs either a collector or codegen-emitted scope
reclamation with escape analysis. That is a project, not a patch, and is
deliberately left open rather than half-built.

The global `Mutex<HashSet<usize>>` on every allocation is a genuine throughput
smell but is **not** worth fixing on its own evidence: the lane that OOM'd the
host took 375 lock acquisitions in a whole run, and the JIT lane's 110 M
acquisitions are uncontended (the interpreter and JIT run single-threaded, and
the 20-core pressure is 128 *separate processes*, which share no mutex).
Sharding it would buy nothing measurable and would not bound the memory.

### Side defect found while building the regression test (not chased)

`fn main() -> i64:` with typed parameters SIGBUSes inside
`simple_driver::interpreter::run_code` on the exact program above, while the same
program with untyped `fn` parameters and the `main = <expr>` form runs clean.
`bin/simple run <file>` on the typed form is fine (it JITs). Untriaged; recorded
here so the next lane does not lose an hour to it.

### Runnable check

`src/compiler_rust/driver/tests/interpreter_heap_reclaim.rs` --
`cd src/compiler_rust && cargo test --release -p simple-driver --test interpreter_heap_reclaim`.

Runs the churn program through the **interpreter** in-process at 500 and 5,000
iterations (10x the work, same live working set) and fails if the allocator
high-water mark grows by more than 4 MB, if more than 4 MB survives the run, or
if more than 10,000 runtime-heap objects get registered. Measured green:
`peak+25,052 B  live+23,610 B  rt_registry=0` for the 5,000-iteration run.
Verified to discriminate: retaining each iteration's array instead of dropping it
makes the same test fail at `peak+27,547,839 B`. The test binary installs its own
`TrackingAlloc` (it is declared in `driver/src/main.rs`, the bin, so
`mem_trace::live()` reads zero in a test binary otherwise) and runs the body on a
64 MB stack (a `#[test]` thread's 2 MB stack dies with SIGBUS in the
interpreter). The compiled/JIT lane is deliberately not covered -- it would fail,
correctly, and the fix for it does not exist yet.

### Claims from the original record that survive unchanged

- The phase-split methodology (log output plateaus while RSS does not) and its
  three eliminations -- not output buffering, not re-parsing, not module-graph
  re-materialisation.
- "Why input size is irrelevant": a 2-line entry costs what the whole tree costs.
- Not fixable in `.spl`; `native_build_worker.spl` has nothing in it to leak.
- `SIMPLE_NATIVE_BUILD_RUST=1` is the route for anything that must succeed.
- Classify rc=255/137 by the absence of the `[TIMEOUT: ...]` line before calling
  it a timeout. (Add: classify rc=1 by reading the error -- here it is `-lSDL2`.)
- Do not mass-kill; reap only PIDs you started.
