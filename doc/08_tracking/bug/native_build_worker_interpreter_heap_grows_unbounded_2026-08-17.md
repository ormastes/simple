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

## Addendum 2026-09-06 (lane GC, aarch64) — reclamation exists, works, and is measured

This addendum **corrects three claims** that had been circulating about this row
and records the first paired before/after measurement of the reclamation path.

### Corrections

1. **"Codegen declares the transient-scope symbols but emits none" is false.**
   `rt_transient_array_scope_begin/_pause/_end` and `rt_transient_heap_promote`
   are registered in `codegen/runtime_sffi.rs:368-371`, in the interpreter
   extern table (`interpreter_extern/mod.rs:414`), and in the JIT symbol table
   (`elf_utils.rs:497-500`). They are **called from `.spl`** at three sites:
   `80.driver/driver_source_pipeline_parsing.spl:94`,
   `80.driver/driver_hir_pipeline_lowering.spl:65`, and
   `10.frontend/_FlatAstBridge/module_assembly.spl:116`. The begin -> pause ->
   promote -> end protocol in `lower_streaming_surface_source` is **fully
   paired on every path**, including each error path, which rolls back the flat
   HIR row count before ending the scope. There is no missing `end`.

2. **"The registry has zero frees, always" is false, and the earlier reading
   that the seed interpreter bypasses the registry was an artifact.**
   `rt_heap_alloc_count` / `rt_heap_free_count` were declared in `.spl` probes
   but registered in **neither** extern table, so they were unbacked externs
   returning nil — indistinguishable from a true 0 (the exact trap in
   `unregistered_extern_silent_nil_2026-08-01`). With them registered, a probe
   allocating 20,000 arrays inside a transient scope reports
   `allocs=40284 frees=20000`: the scope reclaimed **exactly** what it tracked.

3. **"`rt_core_reclaim_transient_immortal` deliberately skips strings"
   (carried from `compiled_checker_multifile_rss_retention_2026-08-03`) is
   stale.** `runtime_native.c` now reclaims a string when
   `RT_CORE_STRING_FLAG_TRANSIENT` is set and `..._FLAG_SHARED` is not, and the
   Rust `free_transient_heap` (`value/collections.rs:1870`) frees strings via
   `rt_string_free`. Measured directly: 800k interpolated strings cost
   **158,820 kB** unscoped and **1,404 kB** scoped, same exit status.

### Measurement (natively compiled Simple, aarch64, this host)

Fixtures do byte-identical work; only the transient scope differs. Peak RSS from
`/usr/bin/time -v`; both fixtures return the same exit status, so the memory
difference is reclamation, not less work.

| fixture | work | peak RSS | wall | exit |
|---|---|---:|---:|---:|
| arrays, no scope | 3e6 arrays | **374,232 kB** | 0.92 s | 160 |
| arrays, scope/1000 | 3e6 arrays | **1,056 kB** | 0.40 s | 160 |
| strings, no scope | 8e5 strings | **158,820 kB** | 1.33 s | 31 |
| strings, scope/1000 | 8e5 strings | **1,404 kB** | 0.65 s | 31 |

**354x** and **113x** reductions, and the scoped build is also **2.3x faster** —
reclaiming early keeps the working set in cache rather than costing time.

### Metric note: the `[heap]` brk figure is ARENA-dependent, not arch-specific

An earlier draft of this addendum claimed the 37 GB `[heap]` brk mapping was
x86_64-specific because this lane's small fixtures showed only a 132 kB brk.
**That was wrong, and a live process on this same aarch64 host disproves it.**
Another lane's Stage-3 worker (PID 3108862, `stage2-admitted/simple` building
`bootstrap_main.spl`) measured, read directly from `/proc/3108862/smaps`:

```
[heap]  Size:  37,313,356 kB
        Rss:   37,171,428 kB
VmRSS (whole process):  44,279,636 kB
```

That is the reported 37 GB brk mapping, reproduced on aarch64, and it independently
re-confirms this row's headline symptom on a currently-running process.

The difference is the glibc **arena**, not the architecture: a small
single-threaded fixture is served from mmap'd arenas, while the long-lived
multi-threaded worker grows its **main** arena via `brk`. Practical consequence
for anyone writing a budget here: measure **both**. A brk-only budget reads as
flat for small or thread-pool-served processes; an RSS-only budget hides which
mapping is responsible. `smaps_rollup` has no `[heap]` line, so the per-mapping
figure must come from `/proc/<pid>/smaps`, and peak from `/usr/bin/time -v`.

### Runnable gate

`scripts/check/check-transient-scope-reclaims.shs` builds both fixtures
natively, requires an identical exit status (correctness before memory), and
gates on a ratio plus an absolute cap. Discrimination is proven, not asserted:

- as shipped: `PASS -- 2 fixture(s) measured, scoped 1056 kB vs unscoped 374224 kB (354x)`, exit 0
- with the scope call sites removed (the pre-fix shape): `FAIL -- ... scoped-over-budget(374088kB>65536kB) reclamation-ineffective(ratio=1x<8x)`, exit 1

### What is NOT fixed, and why

**No new reclamation point was added to the compiler.** Coverage is
`80.driver` (2 files) and `10.frontend` (1 file); `20.semantic`, `30.hir`,
`40.mir`, `50.mir`, `60.opt` and `70.backend` have **zero** transient scopes.
Adding one there was not done because it could not be **measured** here. The
precise blocker, after two corrections to this lane's own first answer:

**Correction A — "the self-hosted compiler cannot be built here" was wrong.**
A first attempt did fail with 167 unresolved runtime symbols (`rt_cranelift_*`
79, `rt_simd_*` 22, `rt_math_*` 18, `rt_io_file_*` 12, `rt_mmap`/`rt_munmap`,
`rt_exec`, `rt_native_build`, `spl_backend_plugin_run_v1`, ...), but that used
the **default runtime archive**. The sanctioned bootstrap path names a bundle
(`bootstrap-from-scratch.sh:1662`). With it, the build succeeds:

```
native-build --runtime-bundle core-c-bootstrap --backend cranelift \
  --source src/compiler --source src/app --source src/lib --entry-closure \
  --mode one-binary --entry src/app/cli/bootstrap_main.spl
=> Build complete: 834 compiled, 0 cached, 0 failed
   Binary: 37,759 KB;  501.9s compile + 101.9s link = 603.8s   rc=0
```

So a self-hosted compiler **does** build on this tree. Any future claim to the
contrary should be checked against a bundle build before it is believed. (A
second lane was in fact building stage3 on this box the whole time, which is
what exposed the error.)

**Correction B — the real blocker is running it, not building it.** The
resulting binary does not start:

```
stage1b.bin: error while loading shared libraries:
  libunwind.so.1: cannot open shared object file
```

This host has only nongnu `libunwind.so.8` (`/usr/lib/aarch64-linux-gnu`, plus
snap copies). LLVM's `libunwind.so.1` is a **different library with a different
ABI**, so symlinking `.so.8` into place would risk a silently wrong unwinder
inside the compiler. Given this row's own standard — a use-after-free or
miscompile in the compiler is worse than the memory — that shortcut was refused,
so the self-hosted compiler could not be executed and no MIR/backend scope could
be measured or shown safe.

**The blocker is therefore a missing `libunwind.so.1` on this host, not the
reclamation design** (which the numbers above show works) and not the runtime
symbol set (which the bundle resolves). Installing LLVM's libunwind, or linking
the stage binary against the unwinder it actually has, unblocks the measurement.

The safe boundary, when the tree can build one, is the one
`lower_streaming_surface_source` already demonstrates: begin -> work -> pause ->
`rt_transient_heap_promote` for **every** escaping root -> end, failing closed
if `begin` returns false. Note `TRANSIENT_HEAP_SCOPE` is `thread_local!` and
`begin` returns false if a scope is already live, so any new site must be
per-thread and must not nest inside an existing scope.

---

## Addendum 2026-09-06 (lane MIR) — the libunwind blocker is resolved, and the MIR lane now has a scope

### The blocker was a `LD_LIBRARY_PATH`, not a missing library

"Correction B" above refused to symlink nongnu `libunwind.so.8` over LLVM's
`libunwind.so.1` — correctly; the ABIs differ and a `dlopen` that succeeds on
the wrong unwinder is silent corruption. **The shortcut was never needed.** LLVM's
own libunwind is already on this host:

```
/home/yoon/dev/llvm/install/lib/aarch64-unknown-linux-gnu/libunwind.so.1
  SONAME libunwind.so.1        18 defined _Unwind_* symbols (incl. _Unwind_RaiseException)
```

so `LD_LIBRARY_PATH=/home/yoon/dev/llvm/install/lib/aarch64-unknown-linux-gnu`
resolves it with the matching ABI and no symlink. Anyone re-running the
self-hosted lane on this box should export that, not install anything.

### Correction to "Correction A": `--runtime-bundle core-c-bootstrap` is NOT sufficient

A build with only that flag compiles all 834 modules and then **fails to link**
with the same 167 unresolved runtime symbols the record blamed on the default
archive (`rt_cranelift_*` 79, `rt_simd_*` 22, `rt_math_*` 18, `rt_io_file_*` 12,
`rt_mmap`/`rt_munmap`, `rt_exec`, `rt_native_build`, `spl_backend_plugin_run_v1`,
...). The bundle name is not what resolves them. The sanctioned invocation
(`bootstrap-from-scratch.sh:1656-1670`, `bootstrap_native_build_main`) also
passes **`--runtime-path "${bootstrap_runtime_authority_path}"`**, i.e.
`src/compiler_rust/target/bootstrap` — which is where `libsimple_native_all.a`
(390 MB) and `libsimple_compiler_backfill.a` live. Without `--runtime-path` the
link cannot succeed no matter which bundle is named. `SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1`
is NOT an answer: the driver states outright that it yields a NULL GOT slot per
name and a SEGV on first call.

### The scope

`MirLowering.lower_module_transient_scoped`
(`src/compiler/50.mir/_MirLowering/module_lowering.spl`), called from the
`--entry-closure` per-module loop in
`src/compiler/80.driver/driver_pipeline_lowering.spl`. Same protocol as
`lower_streaming_surface_source`: begin -> lower -> pause -> promote every
escaping root -> end, with every `return Err` path closing the scope first and
refusing to hand back the module it would otherwise have returned.

**Escape set, enumerated — this is what makes the boundary safe, and the reason
one whole path is excluded rather than scoped:**

1. the returned `MirModule` — promoted;
2. everything `lower_module` writes into the lowering owner. `MirLowering` has
   **97 fields** and the `--entry-closure` loop shares ONE instance across all
   modules, so `errors`, `composite_layout_*`, `struct_field_*`, `builder` and
   `external_layout_traces` all accumulate across the boundary. The owner is
   promoted **as a whole** rather than by a hand-written field list: a list that
   drifts one field behind the struct is a use-after-free, not a missed
   optimisation, and this struct demonstrably grows.
3. module-level mutable globals. On the non-ambient-bootstrap path there are
   **none reachable**, measured rather than assumed: 50.mir's only non-bootstrap
   heap-typed globals are `mir_data.spl:_mir_trace_scope_slot` (an `[i64]` whose
   writes store no heap value) and `mir_bitfield.spl:BITFIELD_REGISTRY`, which
   has **no write site anywhere in the tree**; 25.traits, 40.mono and 30.types
   declare no heap-typed globals at all; the only 35.semantics import into
   50.mir is the bool reader `rt_hal_compilation_requires_finalize`; the only
   15.blocks import is the `BlockValue` type; and none of the seven std modules
   50.mir imports declares a module-level `var`.

**Ambient bootstrap (`SIMPLE_BOOTSTRAP=1`) is deliberately EXCLUDED.** That path
writes the flat `_bootstrap_mir_*` arrays (`_MirLowering/bootstrap_globals.spl`),
`mir_data.spl`'s `_bootstrap_fn_*` dicts and `_bootstrap_type_runtime_names`.
None of those is reachable from either promoted root, so reclaiming the arena
there would dangle them. That escape set is not proven, so the scope is not
taken and the path runs byte-for-byte as before. **Consequence, stated plainly:
the sanctioned bootstrap lane (which sets `SIMPLE_BOOTSTRAP=1`) is still
uncovered** — including the Stage-3 worker whose 37,171,428 kB `[heap]` mapping
is this row's headline symptom. Extending the scope to that path means adding
promotion accessors for those ~30 flat registries, in the shape of
`driver_promote_frontend_registry_owners()`; it is the obvious next lane and is
not done here.

### Runnable gate

`scripts/check/check-mir-transient-scope-boundary.shs` — a ratchet on the CALL
SITE and its pairing discipline, which is the property that was missing.
`check-transient-scope-reclaims.shs` proves the runtime mechanism reclaims and
stays green while nothing on the compiler's hot path calls it; this one fails in
exactly that state. Nine invariants, `--selftest` fatal and first (6 fixtures,
including the pre-fix shape, an unclosed error path, a missing owner promotion
and a removed ambient-bootstrap guard). Verified against the real tree, not only
fixtures: on the committed pre-fix content of the two files it reports
`FAIL — 3 invariant(s) checked ...: driver-entry-closure-loop-not-scoped;
driver-still-calls-unscoped-lower_module; wrapper-missing` (exit 1), and on the
fixed tree `PASS — 9 invariant(s) checked` (exit 0).

### Measurement — and the negative result that matters more than the scope

Paired runs of the **same** 24-module generated closure (25 modules lowered;
`[build] mir 25/25` reached in both), seed
`/home/yoon/.cargo-target-mir/release/simple` built from this worktree,
`--entry-closure --threads 1`, sampled every 2 s from `/proc/<pid>/status` and
`/proc/<pid>/smaps`. Both runs end `rc=1` at `native_compile` on the SAME cause
(`error: semantic: unknown extern function: rt_secure_temp_dir` — the seed's
interpreter extern table, another lane's row), so the work performed is
identical and the comparison is honest:

| run | peak VmRSS | `[heap]` Rss | wall | mir mark | rc |
|---|---:|---:|---:|---|---:|
| pre  (no MIR scope) | **3,520,180 kB** | 8 kB | 168 s | mir 25/25 | 1 |
| post (MIR scope)    | **3,521,688 kB** | 8 kB | 160 s | mir 25/25 | 1 |

**0.04% apart — noise. The scope reclaims nothing in this lane, and the reason
is structural, not a defect in the scope.** `rt_transient_array_scope_*` frees
only what `track_transient_heap` recorded, and that hook sits in the Rust
`simple_runtime` allocators (`rt_array_new`/`rt_string_new`/`rt_dict_new`/
`RuntimeObject`...). In the **seed interpreter** the compiler's own values are
interpreter-side values that never pass through those allocators, so the scope's
object list is essentially empty and `end` frees essentially nothing. This is
the same fact this row already states as the root mechanism — "**self-hosted**,
`rt_array_new`/... resolve into the Rust `simple_runtime`" — read in the other
direction, and it is why the existing 354x/113x numbers were measured on
**natively compiled** fixtures.

**Consequence for anyone continuing this: the interpreted lane cannot measure a
compiler-side transient scope at all.** Do not repeat this measurement; it will
always read as noise. The scope must be measured with a self-hosted (natively
compiled) compiler.

`[heap]` brk read 8 kB in both runs, confirming this row's own arena warning:
this process is served from mmap'd arenas, so a brk-only budget is vacuous here.
Peak RSS is dominated by the ~3 GB the seed spends loading and interpreting the
whole compiler graph, which no per-module scope touches.

### What still blocks the self-hosted measurement (not libunwind any more)

All 834 modules compile (643 s cold, 23 s warm from the content-keyed object
cache), then the **link** fails with the 167 unresolved runtime symbols listed
above, with `--runtime-bundle core-c-bootstrap` AND `--runtime-path` AND
`SIMPLE_RUNTIME_PATH` all pointing at `src/compiler_rust/target/bootstrap`
(which does contain `libsimple_native_all.a`, 390 MB). Reading
`native_project/config.rs:375-395`, `is_authorized_stage4_compiler_entry()` is
checked BEFORE `bootstrap_hosted_native_all_runtime(...)` and returns the
core-C archive alone, so on this entry the `native_all` archive is never
consulted. That is runtime-archive/linker selection — a different lane's
territory — so it was left alone rather than worked around;
`SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1` is explicitly NOT an answer, the driver
itself states it yields a NULL GOT slot per name and a SEGV on first call.

**Therefore, stated plainly: the MIR scope is landed and gated, but its memory
effect is UNMEASURED.** The 354x/113x figures in the earlier addendum belong to
the runtime mechanism, not to this boundary, and must not be re-quoted as if
they did. The first thing to do on this row is a self-hosted build once the
archive selection above is fixed, then re-run the paired closure with it.

**And the same fact bounds the CORRECTNESS evidence, not just the memory
evidence.** Because the interpreter's values never enter the scope's object
list, the paired runs above exercised `begin`/`pause`/`promote`/`end` as calls
but never exercised the FREE path — nothing was reclaimed, so nothing could
dangle. What they do establish is that the change is behaviour-neutral through
parse/HIR/MIR/native_cache: the modified compiler lowers all 25 modules
(`[build] mir 25/25`), emits no scope-failure diagnostic, and stops at the same
place with the same rc as the unmodified one. Producing a runnable binary from
the modified pipeline was attempted on this host and is not possible right now:
`--backend cranelift` needs `rt_secure_temp_dir` (missing from the seed's
interpreter extern table), `--backend llvm-lib` fails `spl_dlopen ... LLVM-C.dll`,
and `--backend c` / `--backend native` are refused outright ("not available in
the pure Simple command path"). So the escape analysis above is argued from an
enumerated write set and NOT yet corroborated by a run that actually frees. Do
not treat this scope as proven safe until a self-hosted compiler has been built
with it and has produced a correct binary.

## Addendum 2026-09-07 — escape-set audit, a real compiled binary through the scoped path, and why the native measurement is still blocked (not by this boundary)

Continuing the row above from a fresh session. Rebased the three landed commits
(`feat(check)` reclaims gate + heap counters, `fix(check)` brk correction,
`feat(mir)` the MIR scope itself, plus the two follow-up `docs(bug)` notes) onto
current `origin/main` (clean cherry-picks, one additive merge conflict in this
file resolved by keeping both addenda). `origin/main` did **not** yet carry any
of this — `check-transient-scope-reclaims.shs` and
`check-mir-transient-scope-boundary.shs` do not exist there and the MIR scope is
still absent, so the prior session's "left undone rather than landed
unvalidated" stance was correct and this row was still open.

### 1. The escape-set audit the prior session called "argued, not corroborated" — now corroborated statically

Re-derived the escape set for `lower_module_transient_scoped` from the actual
call graph rather than trusting the commit message's enumeration:

- **`rt_transient_heap_promote` is genuinely transitive.**
  `collections.rs:1921-1971` walks Array elements, Tuple elements, Dict
  keys+values, `RuntimeObject::fields()` (covers struct/class instances,
  therefore every field of `self`), Closure captures, and Enum payload
  (`transient_heap_children`, `collections.rs:1839-1885`). Promoting `self` as a
  whole is therefore sound: no field of the 97-field `MirLowering` struct can be
  missed by a hand list, because there is no hand list.
- **The input `module: HirModule` is never mutated in place** by anything
  `lower_module` reaches. Grepped every `<ident>.<field> =` and
  `<ident>.<field>.(push|insert|remove|clear)(` pattern across all of
  `src/compiler/50.mir/**` for the HIR-typed parameter names in scope
  (`module`, `func`, `struct_def`, `class_def`, `hir_func`, `raw_func`,
  `hir_module`). Every hit resolves to `self.builder.module` (the OUTPUT
  `MirModule`, reached via the copy-modify-reassign idiom `var m =
  bldr.module; m.x = ...; bldr.module = m`) or to `self.module` on
  `MirModuleBuilder` — never to the HIR argument. This is the exact bug shape
  the row's own precedent (`module_surfaces_freeze` UAF) warns about, and it
  does not recur here: the only escape roots this boundary needs are the ones
  already promoted (`lowered`, `self`).
- **No cross-thread scope sharing.** The `--entry-closure` loop
  (`driver_pipeline_lowering.spl:273-303`) is a plain sequential `while`, single
  `direct_lowering` instance, no thread/actor spawn anywhere in it.
  `TRANSIENT_HEAP_SCOPE` is `thread_local!`, so this is moot here, but worth
  recording since it is exactly the kind of assumption that silently breaks if
  someone later parallelises the loop.

No new defect found; the boundary as landed is sound for the entry-closure call
site specifically. The two OTHER `lower_module` call sites in the same file
(bootstrap fixed-path at line ~234, the non-entry-closure fallback loop at line
~328) remain deliberately unscoped, same as the prior session's design — not
audited to the same depth here, out of scope for this pass.

### 2. A real, running native binary through the scoped path (req. 2), not just a same-rc replay

Rather than repeat the prior session's 24-module `--entry-closure` replay (which
only proves "stops at the same place"), built an actual runnable artifact
through the modified pipeline. `SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1` makes the
entry-closure branch — and therefore `lower_module_transient_scoped` — the code
path for *any* native-build, including a single trivial file, since
`driver_pipeline_lowering.spl:239 if self.ctx.sources.len() > 0` always holds:

```
$ SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1 \
    /home/yoon/.cargo-target-mir/release/simple native-build hello.spl -o hello.out
Linked: .../hello.out (34 KB) via clang
$ ./hello.out
hello from scoped MIR lowering
$ echo $?
0
```

This is a genuine improvement on the prior session's evidence: a real linked,
executed, correct native binary produced via the scoped call site, not a run
that merely reaches the same failure point. It is still an **interpreted-seed**
compile (the seed's own Rust frontend/backend do the work; `MirLowering` is
interpreted `.spl`), so it still only proves the FIRST half of req. 2
(behaviour-neutral, produces a correct binary) — the reclamation-under-native-
execution question (req. 1, the free path) is separate and addressed next.

### 3. Native RSS/brk measurement of THIS boundary: still blocked, narrower gap than reported, still not worth the risk

Re-ran the runtime-mechanism gate fresh (not reused numbers) to confirm the
underlying primitive still reclaims on this host/build:
`check-transient-scope-reclaims.shs` — `PASS -- 2 fixture(s) measured, scoped
1036 kB vs unscoped 374232 kB (361x), identical exit status 124` (`--selftest`
also green). This is the array/string mechanism, proven again, not the MIR
boundary — restated here only so the two are not conflated.

Attempted a smaller alternative to the full self-hosted bootstrap the prior
session was blocked on (167 unresolved symbols): natively compiling a tiny
probe that only `use compiler.mir._MirLowering.module_lowering.*` (not the
whole compiler + LLVM backend). Import resolution and full frontend
compilation of the entire `50.mir` + transitive `20.hir`/`00.common` dependency
graph **succeeded** — a real improvement in diagnosis over "no self-hosted
compiler can be built here" — but the **link** still fails, now on a smaller,
different 59-symbol set (`rt_math_*`, `rt_simd_*`, `rt_coverage_*`, `rt_mmap`/
`rt_msync`/`rt_munmap`, `rt_file_lock`/`rt_file_mmap_read_bytes`, `rt_exec`,
`rt_process_run_with_limits`, others) pulled in transitively by modules 50.mir
imports, not by anything the transient scope touches. `SIMPLE_ALLOW_UNRESOLVED_
RUNTIME=1` would link it, but per this row's own prior finding that yields a
NULL GOT slot per name and a SEGV on first call through one of them — the exact
mechanism that crashed every self-hosted stage binary on hello world in the
`rt_unwrap_or_trap` incident (2026-08-21) referenced above. Building a synthetic
`HirModule` by hand to drive `lower_module_transient_scoped` without the
frontend was also considered and rejected: the code's own comments record that
a hand-duplicated `MirLowering` constructor once drifted 8 fields behind the
struct and silently nil-filled the rest
(`native_build_entry_struct_construction_buildfail_2026-07-20`), i.e. hand-built
HIR/MIR structs are a known landmine in this codebase, and a wrong-by-
construction fixture would produce a measurement that looks real and isn't.

**Conclusion, stated as plainly as the prior session's:** this is genuinely
closer than 2026-09-06 left it (167 unresolved symbols -> 59, all outside the
scope's own dependency set; a real executed binary through the scoped path
where before there was only a same-rc replay) but the native RSS/brk
measurement of the MIR boundary specifically remains blocked on runtime-archive
completeness — a linker/runtime-archive-selection concern, not a reclamation-
design concern, and out of this session's scope per the task boundary (the
sibling backend/runtime-archive lane owns that surface). Per this row's
standing rule — a use-after-free in the compiler is worse than the memory it
saves — landing an unmeasured-but-statically-audited scope, rather than forcing
a measurement through `SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1`, is the correct
tradeoff.

### 4. What this session adds to the gate surface

No new gate script; `check-mir-transient-scope-boundary.shs` (landed
2026-09-06) already does the job req. 3 asks for. Re-verified rather than
re-built: `PASS — 9 invariant(s) checked` on the fixed tree,
`FAIL — 3 invariant(s) checked ...: driver-entry-closure-loop-not-scoped;
driver-still-calls-unscoped-lower_module; wrapper-missing` (exit 1) when pointed
at `origin/main`'s pre-fix content via `--root` — discrimination re-proven
against the real tree, not only its own fixtures.

## Addendum 2026-09-07 (session 2) — the second named-uncovered call site is now scoped; the third (ambient bootstrap) stays open with its blocker unchanged

Continuing from the audit above. Of the two `lower_module` call sites this row's
own MIR addendum named as "remaining, deliberately unscoped" (bootstrap
fixed-path ~line 289-303, non-entry-closure fallback loop ~line 391-414 in
current line numbers), one is now closed.

### 1. The non-entry-closure fallback loop is scoped

`driver_pipeline_lowering.spl`, the `if self.ctx.sources.len() <= 0:` branch
(reached when the driver has HIR modules but no populated `ctx.sources` list —
distinct from both the bootstrap-fixed branch above it, which returns first,
and the `--entry-closure` branch, which requires `sources.len() > 0`). Before:
`var mir_module = lowering.lower_module(hir_module)`, one shared `lowering`
instance across `self.ctx.hir_modules`, never reclaimed — the same
immortal-arena shape the entry-closure loop had before 2026-09-06. Changed to
`lowering.lower_module_transient_scoped(hir_module)`, with the same fail-closed
handling as the entry-closure site: an `Err` adds a compile error and returns
`false` without touching `self.ctx.mir_modules[name]`.

**Escape set: identical to the audited entry-closure boundary, verbatim, for a
structural reason rather than by re-argument.** `lower_module_transient_scoped`
(module_lowering.spl:1213) is the same function called from both sites, with
the same three-part contract: (1) the returned `MirModule`, promoted; (2)
everything `lower_module` writes into the `MirLowering` owner, promoted by
promoting the owner as a whole (`promote_transient_owner`, walks all 97 fields
transitively — no hand list to drift); (3) module-level mutable globals, none
of which are reachable from `lower_module` on the non-ambient path (the 2026-09-07
census earlier in this file already re-derived this by grepping every mutation
site under `src/compiler/50.mir/**`, and that census does not vary by caller —
it is a property of what `lower_module` touches, not of which loop calls it).
**The critical safety property is that `lower_module_transient_scoped` checks
`self.ambient_bootstrap_enabled()` internally and falls back to plain
`self.lower_module(module)`, unscoped, whenever `SIMPLE_BOOTSTRAP=1`** — so this
new call site never attempts to reclaim the arena while the flat
`_bootstrap_mir_*` / `_bootstrap_fn_*` / `_bootstrap_hir_*` registries (whose
reachability is proven NOT established, see below) could be live, regardless of
which of the two branches reaches it. This is why the fix is "nearly free": no
new escape-set argument was needed, only reuse of one already audited.

**Live-repro caveat, stated rather than glossed over.** A concrete input that
drives `self.ctx.sources.len() <= 0` while `self.ctx.hir_modules` is populated
was not found in this session (grepped `src/compiler/80.driver/*.spl` and
`src/compiler/80.driver/bootstrap_api*.spl` for a caller that fills
`hir_modules` without also filling `sources`; none surfaced, meaning this
branch's live trigger is likely an internal driver-API/test-harness compile path
rather than the CLI `native-build`/`run` entry points this session's fixtures
exercise). The change is therefore verified STATICALLY (identical contract,
identical callee, fail-closed on error) and by the fact that it does not alter
any other code path in the file — not by a paired before/after RSS run of this
specific branch. Do not read the RSS numbers in the runtime-mechanism section
below as measuring this boundary; they re-confirm the underlying primitive
only, exactly as the prior addendum's own caveat about the MIR boundary said.

### 2. Ratchet extended

`check-mir-transient-scope-boundary.shs` gained two invariants (now 11, up from
9): `driver-fallback-loop-not-scoped` (the fallback loop must call
`lowering.lower_module_transient_scoped(hir_module)`) and
`driver-fallback-still-calls-unscoped-lower_module` (it must not also retain
the bare `lowering.lower_module(hir_module)` call — grepped on the exact
receiver/argument pair so the bootstrap-fixed branch's legitimate bare call,
`bootstrap_lowering.lower_module(bootstrap_hir)`, is not a false positive). A
seventh selftest fixture (`fallback_prefix`) isolates this from the
entry-closure fixtures and proves the two new invariants alone catch the
pre-fix fallback shape. Verified against the real tree:
`sh scripts/check/check-mir-transient-scope-boundary.shs --selftest` ->
`PASS — 7 selftest fixture(s) checked`; against the current (fixed) worktree ->
`PASS — 11 invariant(s) checked`; against `origin/main`'s committed content (git
show into a scratch tree, `--root`) -> `FAIL — 11 invariant(s) checked ...:
driver-fallback-loop-not-scoped; driver-fallback-still-calls-unscoped-lower_module`
— discrimination proven on the real pre-fix tree, not only synthetic fixtures.

### 3. The third call site (bootstrap fixed-path, `SIMPLE_BOOTSTRAP=1 and not
STAGE4`, line ~289-303) is deliberately left unscoped, and switching its
receiver to `lower_module_transient_scoped` would be a no-op

That branch's own guard condition IS `SIMPLE_BOOTSTRAP=1`, so
`lower_module_transient_scoped` would immediately observe
`ambient_bootstrap_enabled()==true` and fall back to plain `lower_module`
every time — there is no state in which this specific call site would ever
scope. Cosmetic substitution was rejected as noise. This branch also lowers
exactly one module (`app.cli.bootstrap_main`) per invocation, not the hundreds
the entry-closure/fallback loops lower, so it is not believed to be a
significant contributor to the 37 GB regardless.

**The actual location of the 37 GB remains the ambient-bootstrap path as a
whole** (the Stage-3 worker that produced the 37,171,428 kB `[heap]`
measurement runs with `SIMPLE_BOOTSTRAP=1`), and it is excluded from every
scope in the tree — not just this one — for the same unresolved reason each
prior session recorded: the flat `_bootstrap_mir_*` registries
(`_MirLowering/bootstrap_globals.spl`), `mir_data.spl`'s `_bootstrap_fn_*`
dicts, and 20.hir's `_bootstrap_hir_*` arrays are read from other parts of the
compiler by name/index after `lower_module` returns, and no census in this
session or prior ones has enumerated their write sites well enough to prove
they are unreachable from a promoted root (the way the non-ambient globals were
proven unreachable). `driver_promote_frontend_registry_owners()`
(`driver_source_pipeline_parsing.spl:257`) was located as the requested
template, but it promotes a DIFFERENT registry set (aspect/effect/rt_criticality/
layer_eq, used by the frontend/parse-phase scope) — it is a pattern to copy, not
a promoter that already covers the bootstrap MIR registries. Writing the
bootstrap-registry equivalent (grep every write site across
`bootstrap_globals.spl`, `mir_data.spl`'s bootstrap dicts, and 20.hir's
bootstrap arrays, confirm none is written from outside 50.mir's reachable call
graph or from a closure/callback, then add a
`driver_promote_bootstrap_mir_registry_owners()`-shaped function and call it
from inside `lower_module_transient_scoped`'s ambient-bootstrap branch instead
of skipping the scope) is a full session's own work, not a same-session
extension of this one, and was not attempted here given the remaining time
budget and the standing rule that an unproven escape set is refused rather than
forced.

### 4. Backend/codegen emission lane: looked at, not scoped, escape set not
attempted

Two other loop candidates were read this session and rejected as targets for
now, both because their escape sets were not judged provable inside this
session's time budget, not because they were found unsafe:

- **`optimize_mir_level` (`driver_pipeline_passes.spl:35`)**, the per-module MIR
  optimization pass (`optimize_module_for_backend`, `60.mir_opt/mir_opt/mod.spl`
  and its full pass pipeline, 1937 lines in `mod.spl` alone plus however many
  pass files it dispatches to). The loop discards the pre-optimization
  `MirModule` and keeps only the returned one, which is a plausible transient-
  scope shape, but a proper escape-set census (every module-level `var` write
  reachable from `pipeline_optimize`, across a much larger and less-audited
  surface than 50.mir) was not done. Undertaking it without doing the grep-based
  census this row insists on would repeat exactly the mistake this row's own
  history warns against.
- **`CodegenPipeline.compile_module` (`70.backend/codegen.spl:715`)**, the JIT
  Cranelift lane. Read and set aside for a different reason: its per-module
  state (`CraneliftCodegenState`) is mostly a handle onto native Cranelift
  compiler state reached via `rt_cranelift_*` externs, not Simple-heap objects
  registered in `HEAP_ALLOCATION_REGISTRY`, so a `.spl`-level transient scope
  around it is unlikely to reclaim the thing this row is about; disposal there
  is `release_codegen_module()` -> `codegen.free_module()`, a different
  (already-explicit) reclamation path, not the immortal-heap defect.

Both are recorded here as the next places to look, not as closed or ruled out.

### 5. Verification, corrected after a re-check found the first pass over-claimed

The first draft of this addendum reused the prior session's
`SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_NATIVE_BUILD_ENTRY_CLOSURE=1 ... native-build
hello.spl` result as proof that a real binary ran through the modified file.
**That reuse was wrong and is retracted.** Re-run with
`SIMPLE_COMPILER_TRACE=1` added (which makes every `log_phase` call —
including `aot:lower_to_mir:module:start/done`, present in the very function
this session edited — print a `[BOOTSTRAP-PHASE]` line): zero such lines were
printed, for either run. `SIMPLE_NATIVE_BUILD_RUST=1` routes the whole build
through the seed's own compiled Rust native pipeline; for a zero-import
`hello.spl` this apparently never touches the interpreted `.spl` driver
(`driver_pipeline_lowering.spl`) at all, consistent with the total wall time
(0.0s compile + ~4s link — far below the 15-30s the record's own reproducer
needs just to load the compiler graph). So that command proves the SEED still
emits correct binaries; it proves nothing about this session's edit, and the
predecessor's 2026-09-07 §2 claim that it "exercises the entry-closure branch"
should be read the same way going forward.

**What was actually run instead, in order of how much it proves:**

1. **Plain `native-build` (no `RUST=1`) and the direct
   `SIMPLE_NATIVE_BUILD_WORKER=1 ... run src/app/cli/native_build_worker.spl`
   reproducer, both against the same `hello.spl`** — both spawn/route through
   the INTERPRETED `.spl` compiler graph (confirmed by the volume of
   cross-module warnings emitted, matching the record's phase-A description),
   and both fail identically: `error: semantic: unknown extern function:
   rt_env_vars` (exit 1), before reaching MIR lowering. **This is a
   pre-existing, unrelated defect, not introduced by this session and not
   fixable within it**: `rt_env_vars` is registered in the codegen SFFI table
   (`codegen/runtime_sffi.rs:1944`) and in `common/runtime_symbols.rs:803`, but
   grepping `src/compiler_rust/compiler/src/interpreter_extern/*.rs` for it
   returns nothing — it was never added to the INTERPRETER's extern table, on
   any seed build available this session (all built 2026-09-06/07 from this
   same tree lineage). Every full-graph interpreted compile is therefore
   currently blocked, independent of anything in this row.
2. **`/home/yoon/.cargo-target-mir/release/simple lint
   src/compiler/80.driver/driver_pipeline_lowering.spl`** — lint does NOT
   execute the interpreted whole-graph pipeline (it is a static frontend pass:
   parse, resolve, type-check), so it is unaffected by the `rt_env_vars` gap
   and DID complete: `Found 0 error(s), 7 warning(s), 0 auto-fix(es) available`.
   All 7 warnings are pre-existing `RAW-RT-001`/`RAW-RT-002` (raw `rt_env_get`
   calls already in the file before this session) and one pre-existing
   duplicate-typed-argument style warning; none names anything this session
   added. This is real evidence the edited file **parses and type-checks
   cleanly** under the actual compiler frontend — it is not evidence the
   fallback loop executes correctly at runtime.
3. `sh scripts/check/check-mir-transient-scope-boundary.shs --selftest` — `PASS
   — 7 selftest fixture(s) checked, scanner discriminates the pre-fix shape`.
4. `sh scripts/check/check-mir-transient-scope-boundary.shs` (this worktree) —
   `PASS — 11 invariant(s) checked, per-module MIR lowering runs inside a paired
   transient scope with both escaping roots promoted`.
5. Same script against `origin/main`'s committed content — `FAIL — 11
   invariant(s) checked ...: driver-fallback-loop-not-scoped;
   driver-fallback-still-calls-unscoped-lower_module`.
6. `SIMPLE_SEED=/home/yoon/.cargo-target-mir/release/simple sh
   scripts/check/check-transient-scope-reclaims.shs` (mechanism re-proof, fresh,
   not reused numbers) — `PASS -- 2 fixture(s) measured, scoped 1052 kB vs
   unscoped 374236 kB (355x), identical exit status 124`. This is the
   array/string primitive, re-confirmed on this host/build; it was never a
   measurement of the fallback-loop boundary and is not claimed as one.

**Stated plainly, matching this row's own standard of not overclaiming:** no
session, including this one, has produced a paired before/after RSS/brk
measurement OR a successful end-to-end run of ANY MIR-lowering transient scope
(entry-closure, fallback, or otherwise) through the fully interpreted
self-hosted pipeline. The entry-closure scope's "real running binary" evidence
from 2026-09-07 needs the same re-check this addendum just gave its own
claim — it was not re-verified with phase tracing in this session, so treat it
as unconfirmed rather than re-affirmed. What IS established for the fallback
loop specifically: it type-checks cleanly, it reuses a callee whose behavior
is unconditionally safe under ambient bootstrap by construction, and the
ratchet gate proves the source-level shape is correct and discriminates the
pre-fix tree. No collector was designed. Per the task's own preference order,
coverage extension was judged reachable and was done first; the ambient-
bootstrap path (§3), the two backend/opt candidates (§4), and — newly found
this pass — the missing `rt_env_vars` interpreter extern (blocks re-verifying
ANY of this by full interpreted execution) are the next things to attempt.
