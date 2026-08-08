# Memory-infra next phase plan (2026-07-29)

Successor to the stage4 lanes plan (L1-L7 complete). Research:
`doc/01_research/runtime/memory_analysis/memory_infra_gap_and_tools_2026-07-29.md`.
Features: `doc/02_requirements/runtime/memory_analysis/feature_per_owner_allocation_attribution.md`,
`feature_backend_memory_infra_toggle.md`.

Cross-cutting requirements (all phases):
1. **Allocator-model coverage** — every mechanism covers the four models
   (malloc-backed nogc, GC tier, index-based arenas/slotmaps, static pools)
   via one instrumentation trait (alloc/free/owner/bytes). A malloc-only
   implementation is an incomplete lane, not a done lane.
2. **Zero-overhead-when-off (HARD RULE).** Any mechanism that adds runtime
   overhead MUST be config/flag-gated and OFF by default: env or
   `--mem-infra` row, checked once at startup (a cached bool, not a per-alloc
   env read). Each lane's exit criteria include a measured before/after run
   with the feature off showing no regression. Debug-tier-default features
   (harden, genarena) must still be individually disableable.

## M1 — attribution (backend-agnostic, LOW)
Per-owner byte accounting at the heap-registry choke point keyed on
CURRENT_EXEC_MODULE; SIMPLE_MEM_ATTR=1 gate; rt_heap_top_owners(n);
memstat --by-owner. Arena slot-allocs and GC allocs feed the same counters
through the trait. Exit: two-module fixture attributes correctly under
interpreter + cranelift native; zero overhead when unset.

## M2 — sampled guard + hardened debug allocator (backend-agnostic, LOW)
GWP-ASan-style: sample 1/N rt_alloc onto guard-paged slots (UAF/overflow
traps with the sampled alloc's owner); Zig-GPA-style debug mode: quarantine +
poison-on-free + canaries. Index-based equivalent: slot poison + delayed
index reuse + generation check (extends L6); GC equivalent: poison on sweep
in debug tier. Exit: seeded UAF fixtures (malloc AND stale-slot AND
after-sweep) each trapped with attribution.

## M3 — `--mem-infra=` interface (plumbing, LOW-MED)
Capability matrix resolution (backend × allocator-model), graceful
degradation notices, --mem-infra-strict, help text; existing envs become
aliases. Exit: acceptance rows in the feature doc.

## M4 — LLVM lane (MED)
`asan` for native test builds; `memprof` emission (-fmemory-profile) with
profile stored for future PGHO feed-back. LLVM-backend-only by design;
cranelift resolves to M2 equivalents. Exit: ASan build catches the M2 malloc
fixture; memprof profile produced for a stage-2 compile of a small corpus.

## M5 — strict interpreter mode (Miri-lite, MED)
SIMPLE_STRICT_MEM=1: uninit-read traps, poison-on-free, arena provenance +
generation enforcement on every index deref (not just tag reads), GC-tier
dangling-survivor checks. Exit: each defect class has a fixture that passes
normally and traps under strict.

## M6 — stdlib generational slotmap (LOW-MED)
`std.mem.gen_arena`: Vale-style generational handles as a library; checks
default-on in debug tier, compiled out in release. Migrate one ECS store as
proof. Exit: stale-handle fixture traps in debug, zero-cost release.

## M7 — GPU lane (CUDA/HIP, MED)
Device-alloc choke point in the gpu/cuda tier SFFI wrappers implements the
same trait (owner-tagged device alloc/free, per-pool stats via
cudaMallocAsync pools / cuMemPoolGetAttribute; NVML device truth).
`--mem-infra=gpu-sanitize` wrapper execs the program under NVIDIA
compute-sanitizer (memcheck/racecheck/initcheck) or ROCm equivalents; trace
mode dumps a PyTorch-memory_viz-compatible snapshot so their interactive
viewer works on our traces. All rows config-gated, off by default. Exit:
seeded device leak + OOB fixtures caught; snapshot opens in memory_viz;
zero overhead with the gate off.

## M8 — `simple mem` CLI (interactive interface, MED) — LANDED ef00d5e2094
One entry point for ALL of the above, per
`doc/02_requirements/runtime/memory_analysis/feature_simple_mem_cli.md`:
`simple mem top|snapshot|diff|trace|gpu|gate` — Simple-TUI interactive top
(live per-owner/per-kind bytes), snapshot diff between two capture files,
trace record + query (data stays in files; CLI is the query surface),
device rows from M7. Speaks to a live process via the existing MCP/socket
plumbing or post-mortem via profile files. Exit: `simple mem trace prog.spl`
then `simple mem top --profile <file>` shows the M1 fixture's owners; TUI
interactive under plain terminal. **Status: verb dispatch complete, all
help-listed verbs dispatch explicitly, unknown verb prints help and exits 1,
`top --once` renders one frame without TUI loop. Spec test/03_system/app/mem_cli_spec.spl: 7/7.**

## WATCH (not scheduled)
LLVM PGHO feed-back once the allocator grows partitioning hooks; HWASan/MTE
on aarch64 boards; OxCaml-style local/unique modes as the long-term static
direction; Fil-C capability ideas.

## Verification culture
Each milestone lands with: fixture-backed spec (SSpec), overhead measurement
(warm run, before/after), and a one-page entry appended to the research doc.

## Overhead measurements (2026-07-29)

Cross-cutting req 2 ("zero-overhead-when-off HARD RULE") measured against the
landed M1 gate: `SIMPLE_MEM_ATTR` in `src/compiler_rust/runtime/src/value/heap.rs`
(cached `OnceLock<bool>`, checked at `note_attr_alloc`/`note_attr_free`/
`set_current_owner`) plus the interpreter hook
(`rt_mem_attr_enabled()` call sites in
`compiler/src/interpreter_call/core/function_exec.rs:560,613,1361`).

**Machine:** shared 32-core box, `load average: 38.81, 37.74, 29.69` at
measurement time (noisy) — medians used throughout, A/B interleaved.
**Binary:** `src/compiler_rust/target/debug/simple` (debug build, `cargo build
--bin simple`, this session's build — no source edits made by this lane).
**Probe:** `/tmp/overhead_probe.spl` — builds a 90,000-element `[text]` array
via `arr = arr.push(...)`, then sums `.len()` over every element; workload
time measured in-process via `rt_time_now_unix_micros()` (excludes process
startup/link overhead).

| Probe | Runs (each) | Median OFF | Median ON | Delta |
|---|---|---|---|---|
| 90k-elem text array push+sum, in-process timer, ABBA-interleaved | 20 | 1302.5 ms | 1779.5 ms | **+36.6%** |
| Same probe, wall-clock (`/usr/bin/time -f %e`), plain interleaved | 7 | 1.42 s | 1.86 s | +31% |
| OFF, `env -u SIMPLE_MEM_ATTR` (inherits full env) | 7 | 1071 ms | — | — |
| OFF, `env -i` clean env (`PATH`+`HOME` only) | 7 | 975 ms | — | — |

Raw in-process elapsed_ms samples (ABBA-interleaved, sorted):
- OFF (n=20): 942, 952, 1002, 1076, 1083, 1122, 1185, 1224, 1260, 1282, 1323,
  1345, 1392, 1476, 1486, 1489, 1501, 1503, 1590, 1780
- ON (n=20): 1336, 1386, 1493, 1538, 1580, 1629, 1693, 1694, 1731, 1760, 1799,
  1806, 1815, 1883, 1919, 1976, 2048, 2079, 2320, 2668

### Findings

1. **OFF is indistinguishable from env-pollution / clean-env baseline.** The
   `env -u` OFF median (1071 ms) and `env -i` clean-env OFF median (975 ms)
   differ by ~9%, well inside the ~940-1780 ms noise band the same OFF
   configuration produces run-to-run on this loaded machine. There is no
   separate "baseline" binary to diff against (in-flight edits elsewhere in
   the tree made a pre-feature rebuild unsafe per the task brief), so this
   lane leans on the code structure instead: the off path is a single cached
   `OnceLock<bool>` read guarding an early return, added at 3 call sites that
   did not exist before M1 and cost nothing when the branch isn't taken:
   ```rust
   static ATTR_ENABLED: OnceLock<bool> = OnceLock::new();
   #[inline]
   fn mem_attr_enabled() -> bool {
       *ATTR_ENABLED
           .get_or_init(|| std::env::var("SIMPLE_MEM_ATTR").map(|v| v == "1").unwrap_or(false))
   }
   ```
   and, at each of the three instrumentation points (`note_attr_alloc`,
   `note_attr_free`, `set_current_owner`, called from the generic alloc/free
   hot path at `heap.rs:236,253,277`):
   ```rust
   fn note_attr_alloc(ptr: usize, bytes: u64) {
       if !mem_attr_enabled() { return; }
       ... // Mutex lock + HashMap insert — never reached when OFF
   }
   ```
   No lock, no map, no thread-local write on the OFF path — matches the plan's
   "cached bool, not a per-alloc env read" requirement. **Verdict: OFF is
   consistent with zero added overhead; not separately provable from a
   pre-feature baseline on this measurement pass, but the noise band swallows
   any OFF-path cost that could exist.**

2. **ON cost is +36.6% (in-process median) on this allocation-heavy workload.** This is
   expected once the code is read, not a surprise: this probe is
   allocation-heavy (90k array pushes; per the "seed `.push()` always clones"
   finding, `arr = arr.push(v)` reallocates/copies the whole backing buffer
   each call, so it's O(N²) allocations), and the ON path takes a global
   `Mutex` lock plus a `HashMap` insert/lookup on **every** heap alloc and
   free while enabled. The gate correctly keeps this cost opt-in (`OFF` by
   default, satisfying the hard rule). M1's ON-path cost is a real,
   allocation-rate-proportional burden, not a rounding error: the per-alloc
   mutex is a fixed cost per operation. Lower-allocation-rate workloads would
   show a smaller percentage, but the cost remains. No sharding attempted yet;
   if lower overhead is needed later, sharding the global lock/map is the
   first place to look. **Current status: OPEN ITEM, measured +36.6%, target <15%.**

### Caveats
- Debug build (`cargo build`, not `--release`); absolute timings are not
  representative of production, but the OFF-vs-ON *delta* is what's being
  measured and both sides ran the same binary/build.
- Shared machine, `load average ~38` on 32 cores — wall-clock noise band is
  wide (~840 ms spread on the OFF distribution alone); medians + 20-sample
  ABBA interleaving used to damp drift, but a fully idle machine would
  tighten both distributions.
- No pre-feature (pre-M1) binary was rebuilt for a true baseline diff, per
  the task brief (avoiding a slow rebuild against a tree with another
  session's in-flight edits) — the "OFF == pre-feature" claim rests on the
  code-structure argument above (§ finding 1), corroborated by, not proven
  by, the clean-env-vs-normal-env OFF comparison.

## Overhead measurement (2026-07-30): landed M1 vs uncommitted RwLock+thread-local-cache redesign

Three prior attempts to quantify `SIMPLE_MEM_ATTR` ON-overhead on this shared,
heavily-loaded box produced three different figures (+36.6% for landed M1
through an interpreter-level probe; ~83-120% for a rejected RwLock+16-shard
design; ~40% for an uncommitted thread-local-cached-pointer redesign). This
pass builds a dedicated, isolated, statistically-grounded harness to settle
which of two *currently real* candidates — the **landed M1** design (single
global `Mutex<AttrState>`, `HashMap<usize,u32>` by-ptr map, on
`origin/main`) vs the **uncommitted working-copy redesign** (`RwLock<AttrRegistry>`
+ 16-shard `Mutex` by-ptr map + per-thread cached `*const OwnerCounters`
pointer, atomics on the hot path, present only in the dirty working copy —
see `git diff FETCH_HEAD -- src/compiler_rust/runtime/src/value/heap.rs`,
447 lines, uncommitted) — actually performs better, and by how much.
**heap.rs's design was not modified by this lane**; both variants measured
below are pre-existing code, read verbatim into isolated build copies.

### Methodology

**Isolation.** The working copy is shared with other active sessions, so
building in place (even transiently swapping `heap.rs` back and forth) risked
corrupting a concurrent session's build. Instead, the whole `compiler_rust`
workspace source (excluding `target/`, ~1.5 GB with the mandatory vendored
crates — this workspace builds `--offline` from `vendor/`, see
`.cargo/config.toml`) plus the external path-dependency `src/runtime/`
(C sources + `runtime/hosted`, ~313 MB) were `rsync`'d twice into
`/tmp/bench_ws/{origin,wc}/`, each built with its own `CARGO_TARGET_DIR` so
neither touched the shared `src/compiler_rust/target/`. `origin/heap.rs` was
replaced with `git show FETCH_HEAD:.../heap.rs`; `wc/heap.rs` was replaced
with the working copy's current (uncommitted) file, byte-for-byte (`diff`
confirmed zero delta both ways after the copy). Each copy was compiled once
with `cargo test --release -p simple-runtime --lib --no-run -- --ignored`
(`abfall`/`ring`/`rayon`/etc. resolve from `vendor/`, no network needed).
Build note for reproduction: a naive `rsync --exclude=target/` also excludes
the vendored `cc` crate's *source* subdirectory `vendor/cc/src/target/` (name
collision, not a build-output dir) — use `--exclude=/target/` (anchored)
instead, or the vendor tree silently loses 4 files and the build fails on a
missing `ar` input with a confusing "No such file" error.

**Probe.** Both `heap.rs` copies already carry (working copy) or were given
(origin copy, added only to the throwaway `/tmp` build, not the repo) matched
`#[ignore]`d benches `bench_alloc_heavy_off`/`_on` that drive the actual
malloc + heap-registry path — `Box::new(HeapHeader::new(...))` →
`register_heap_ptr` → `unregister_heap_ptr` → `drop` — for 3,000,000
alloc+free pairs per trial (both copies' `n` aligned to 3,000,000; the
working copy's checked-in default was 1,000,000 in its own bench, bumped only
in the `/tmp` measurement copy). This exercises the *whole* alloc/free path
including both designs' attribution hooks, not the attribution call in
isolation — closer to the M1 finding's own stated intent. Each trial's
elapsed time and derived ns/pair is printed via `eprintln!` and parsed by the
harness. Per-pair op count: 3,000,000 (every OFF trial: 328-438 ms observed;
every ON trial: 488-752 ms observed — both comfortably over the ~200 ms
floor).

**A/B/A/B interleaving.** `ATTR_ENABLED` is a `OnceLock<bool>` latched once
per process, so ON/OFF cannot be toggled inside one process — true
interleaving requires a fresh process per trial. `/tmp/bench_ws/run_ab.sh`
runs `OFF, ON, OFF, ON, ...` as 2×15 separate process invocations per binary
(`env -u SIMPLE_MEM_ATTR` for OFF, `SIMPLE_MEM_ATTR=1` for ON), writing one
CSV row per trial with `ns_per_pair`. Two independent 15-pair replicates were
run per binary (run1, run2) back-to-back, then pooled (n=30) for the primary
comparison. `/proc/loadavg` was captured at the start and end of every
15-pair pass.

**Machine load** (shared 32-core box): origin-run1 start `27.72 29.78 27.58`
→ end `27.11 29.57 27.54`; wc-run1 start `27.11 29.57 27.54` → end
`25.58 29.12 27.43`; origin-run2 start `21.94 27.43 26.94` → end
`22.95 27.37 26.93`; wc-run2 start `22.95 27.37 26.93` → end
`21.41 26.81 26.75`. Load was stable (~22-30) and did not trend
monotonically across the run order, so A/B/A/B interleaving (rather than a
before/after split) is what makes the OFF-vs-ON deltas trustworthy here.

### Results (ns per alloc+free pair, median with IQR)

| Design | Run | n pairs | OFF median | OFF IQR | ON median | ON IQR | ON-vs-OFF delta |
|---|---|---|---|---|---|---|---|
| M1 (landed, origin/main) | run1 | 15 | 120.6 | 9.8 | 183.2 | 13.7 | **+51.9%** |
| M1 (landed, origin/main) | run2 | 15 | 139.5 | 22.4 | 196.1 | 38.0 | **+40.6%** |
| M1 (landed, origin/main) | **pooled** | **30** | **126.4** | **24.1** | **190.3** | **23.2** | **+50.5%** |
| Working-copy redesign (uncommitted) | run1 | 15 | 127.4 | 24.9 | 186.4 | 20.3 | **+46.3%** |
| Working-copy redesign (uncommitted) | run2 | 15 | 117.7 | 6.1 | 175.0 | 16.8 | **+48.7%** |
| Working-copy redesign (uncommitted) | **pooled** | **30** | **119.8** | **14.3** | **176.2** | **21.4** | **+47.1%** |

Raw per-trial CSVs: `/tmp/bench_ws/results/{origin,wc}_run{1,2}.csv` and
pooled `{origin,wc}_pooled.csv` (throwaway, not committed — reproduce via
`/tmp/bench_ws/run_ab.sh <binary> <label> 15` against the two isolated
builds described above).

A rank-based two-sample check (Mann-Whitney U, normal approximation) on the
pooled ON samples gives `z ≈ -2.74` (working-copy ON times are the lower
group) — a real, if modest, signal that the working-copy redesign's ON path
is genuinely faster, not noise. The pooled OFF samples give `z ≈ -1.63`,
not distinguishable at the same threshold — consistent with both designs'
OFF path being the same "single cached-bool early return," as required.

### Findings

1. **Neither design reaches the <15% target.** Pooled medians: M1 landed
   +50.5%, working-copy redesign +47.1%. Both are far above the M2 exit
   bar. This is a load-bearing conclusion, not an artifact of the specific
   run picked — both 15-pair replicates for both designs independently land
   in the 40-52% band, and the pooled n=30 IQRs (23.2 and 21.4 ns) are
   narrow relative to the ~64 ns gap between OFF and ON medians for either
   design.
2. **The working-copy redesign is a modest, probably-real improvement over
   the landed M1 design — not a large one.** Pooled delta drops from +50.5%
   to +47.1% (≈3.4 percentage points, ≈7% relative), and the Mann-Whitney
   check on ON-path times supports this being a genuine (if small) effect
   rather than pure noise. It is **not** the dramatic win a "cut the lock
   count from 2/pair to a lock-free atomic path" design might suggest on
   paper — in this single-threaded, uncontended benchmark, an uncontended
   `Mutex::lock()` is already cheap (no OS futex wait), so replacing it with
   a `RwLock::read()` (for `set_current_owner`, off the hot path) plus a
   sharded `Mutex` (still on the hot path, once per alloc and once per free,
   same lock-op *count* as M1) mostly trades a `SipHash`-hashed
   `HashMap<usize,u32>` for a custom-multiply-hashed sharded map and moves
   the four counter updates (live/peak/allocs) off the lock onto atomics —
   real wins, but on top of a floor cost (malloc + the existing heap
   registry Mutex, present in *both* OFF numbers) that both designs still
   pay identically.
3. **This probe's absolute percentages are structurally not comparable to
   the previously-recorded +36.6% M1 figure**, and that is expected, not a
   contradiction: the 2026-07-29 entry above measured a 90k-element
   `[text]` array push+sum running *through the interpreter*, where
   interpreter dispatch overhead dilutes the attribution hooks' share of
   total time. This pass measures `register_heap_ptr`/`note_attr_alloc` in
   a tight Rust loop with no interpreter in between, isolating the
   attribution mechanism itself — a higher, but more mechanism-accurate,
   percentage. Both are legitimate measurements of different things; an
   end-to-end `.spl` workload's overhead will sit somewhere below this
   pass's number and (per the 07-29 entry) somewhere near or above the
   90k-array-push figure depending on allocation density.
4. **Zero-overhead-when-off holds for both designs**, and holds *equally*
   for both: OFF medians (M1 126.4 ns, redesign 119.8 ns pooled) sit within
   each other's IQR and are not separated by the significance check, both
   dominated by the same underlying malloc + `register_heap_ptr` registry
   cost that exists with or without `SIMPLE_MEM_ATTR`.

**Conclusion for the M2/M1 decision:** on this measurement, the uncommitted
redesign is a small, plausibly-real improvement (~3-8 percentage points,
one-shard-mutex-plus-atomics vs one-global-mutex) over the landed M1 design,
but **neither reaches the <15% target**, and the redesign's added complexity
(RwLock, 16-way sharding, custom hasher, per-thread cached raw pointer with
an `unsafe` dereference, +130 net lines) is a lot of surface area for a
single-digit-percentage-point win in this benchmark. Getting under 15% needs
a structurally different approach (e.g., batched/sampled attribution, or
per-thread accumulation with periodic flush instead of per-alloc
synchronization) rather than another lock-shape variant — that is the next
open question for M2, not a design already in hand.
