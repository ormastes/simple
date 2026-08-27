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

## M8 — `simple mem` CLI (interactive interface, MED)
One entry point for ALL of the above, per
`doc/02_requirements/runtime/memory_analysis/feature_simple_mem_cli.md`:
`simple mem top|snapshot|diff|trace|gpu|gate` — Simple-TUI interactive top
(live per-owner/per-kind bytes), snapshot diff between two capture files,
trace record + query (data stays in files; CLI is the query surface),
device rows from M7. Speaks to a live process via the existing MCP/socket
plumbing or post-mortem via profile files. Exit: `simple mem trace prog.spl`
then `simple mem top --profile <file>` shows the M1 fixture's owners; TUI
interactive under plain terminal.

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

2. **ON cost is NOT under ~5% on this workload — it is ~31-37%.** This is
   expected once the code is read, not a surprise: this probe is
   allocation-heavy (90k array pushes; per the "seed `.push()` always clones"
   finding, `arr = arr.push(v)` reallocates/copies the whole backing buffer
   each call, so it's O(N²) allocations), and the ON path takes a global
   `Mutex` lock plus a `HashMap` insert/lookup on **every** heap alloc and
   free while enabled. The gate correctly keeps this cost opt-in (`OFF` by
   default, satisfying the hard rule), but M1's ON-path cost model should be
   documented as "real, allocation-rate-proportional," not "small" — a
   lower-allocation-rate workload would show a smaller percentage, but the
   per-alloc mutex is a real fixed cost per operation, not a rounding error.

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
