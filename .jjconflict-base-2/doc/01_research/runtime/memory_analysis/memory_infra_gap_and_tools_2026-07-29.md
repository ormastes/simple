# Memory-analysis infra: gap vs Rust, tool/language survey (2026-07-29)

Follow-up to `doc/01_research/compiler/bootstrap/stage4_memory_ownership_research_2026-07-29.md`
(lanes L1-L7). This doc: (1) gap list vs the Rust ecosystem, (2) web survey of
tools + language features, (3) recommendations feeding the plan at
`doc/03_plan/runtime/memory_analysis/memory_infra_next_phase_plan_2026-07-29.md`.

## 1. Gap list vs Rust

What we now have at/above par:
- Always-on per-kind byte counters (header + aux backing buffers) with zero
  setup — Rust needs jemalloc stats/dhat wiring for the same.
- Arena generation-ID stale-index diagnostics — stock Rust has NO diagnostic
  for stale `Vec` indices (they escape the borrow checker); slotmap is opt-in.
- CI RSS gate + smaps_rollup sampler (`src/app/memstat`).
- Hosted alloc registry: double-free/foreign-pointer refusal.

Gaps (ranked by practical pain):
1. **Call-site/owner attribution** — counters say *what kind* grew, not *who*
   allocated. Rust: heaptrack/bytehound/dhat flamegraphs. → Feature filed:
   `doc/02_requirements/runtime/memory_analysis/feature_per_owner_allocation_attribution.md`.
2. **Static prevention** — no borrow checker; UAF/aliasing prevented only by
   tier discipline. Structural, not tooling.
3. **UB/uninit detection** — no Miri/MSan equivalent. (But see §3: our
   interpreter can play Miri's role.)
4. **Production-grade sampling detector** — no GWP-ASan-style guard-page
   sampling; bugs must reproduce under a debug tool.
5. **Leak attribution** — live counts exist; no per-source leak report (LSan).
6. **Allocator hardening** — no quarantine/canaries (Scudo, Zig GPA safety).
7. **Profile-guided heap optimization** — nothing like LLVM MemProf/PGHO.

## 2. Tool survey (web, 2026-07)

Backend-agnostic (allocator/runtime-level — work under interpreter, Cranelift, LLVM):
- **GWP-ASan** (LLVM/Scudo/Android; Trail of Bits 2025-12 writeup): samples a
  tiny fraction of allocations onto dedicated guard-paged slots; catches
  UAF/overflow in production at ~zero overhead (~40 KiB fixed). Allocator-level
  — `rt_alloc` is our single choke point, so a Simple port is LOW cost.
  **ADOPT** (top pick).
- **bytehound / heaptrack**: intercept + stack-trace every allocation; cheap
  custom unwinder (bytehound), heaptrack-GUI interop. Work on our native ELF
  binaries TODAY via LD_PRELOAD; no integration needed, document usage.
  **ADOPT-as-docs**; ADAPT-IDEA: bytehound-style cheap sampled unwinder for
  the attribution feature's stack mode.
- **Zig GeneralPurposeAllocator safety mode**: debug allocator with
  never-reuse + quarantine + double-free/UAF detection. LOW cost in
  `rt_alloc`. **ADOPT** (debug tier default).
- **rr / Pernosco**: record-replay debugging; works on our binaries now.
  Document. **ADOPT-as-docs**.
- **eBPF continuous profilers (Parca etc.)**: fleet-scale; not our scale.
  **SKIP** for now.
- **Valgrind massif / DHAT**: works today on native binaries; slow; superseded
  by the above for routine use. Keep as escape hatch.

LLVM-backend-only (need codegen instrumentation passes):
- **ASan/LSan**: full redzone+shadow checking; for test builds only (2-3x
  slow). **ADOPT behind `--mem-infra=asan`** (LLVM lane).
- **LLVM MemProf / PGHO** (llvm.org/docs/MemProf.html): heap profiling fed
  back into compilation; allocation hotness/lifetime → layout/allocator hints
  (tcmalloc interfaces; allocator-partitioning RFC active 2025). MED cost.
  **ADAPT later** — highest long-term payoff of the LLVM-only set.
- **HWASan / ARM MTE**: hardware tag checking, aarch64 only. **WATCH** (board
  work makes this interesting later).
- **MSan**: needs whole-world instrumentation incl. runtime — HIGH cost.
  **SKIP**; strict-interpreter mode covers uninit reads cheaper.
- **Fil-C / InvisiCaps** (fil-c.org; LWN 2025): fanatically-compatible
  memory-safe C via invisible capabilities; 1.5-4x overhead. Wrong layer for
  us (we own the language), but the capability-on-load idea is noted.
  **SKIP / WATCH**.

## 3. Language features survey

- **Vale generational references**: every object carries a generation;
  references remember it; dereference asserts match. We already built exactly
  this for the AST arena (L6). **ADAPT: generalize** — stdlib generational
  slotmap (`std.mem.gen_arena`) with checks default-on in debug tier;
  language-level `&gen T` deferred.
- **Miri's role via our interpreter**: we ALREADY have the reference
  interpreter. A `SIMPLE_STRICT_MEM=1` mode — poison-on-free, uninit-read
  traps, arena-provenance checks — is a Miri-lite at MED cost, no codegen
  work. **ADOPT** (unique structural advantage).
- **OxCaml modes (local/unique/once, Jane Street 2024-26)**: inferred modes
  enabling safe stack allocation + uniqueness; fully backward compatible.
  Fits Simple's tier system (nogc tiers ≈ locality regions). MED-HIGH typeck
  cost. **ADAPT-IDEA, long-term** — the most promising static direction for
  Simple, cheaper than a full borrow checker.
- **Zig defer/errdefer + allocator-passing (Odin/Jai context allocator)**:
  allocator-passing is already close to our tier model; no action.
- **Koka Perceus / Lobster RC elision / Nim ORC**: RC-optimization work —
  relevant to gc tiers later, not to bug-finding. **SKIP** here.
- **Rust Polonius / capture checking (Scala) / Linear types (Austral,
  Haskell)**: full static ownership — **SKIP** (cost ≫ benefit given tiers).
- **Verona/Pony regions & capabilities**: concurrency-ownership; revisit with
  actor tier hardening, not memory analysis.

## 3b. The allocator-model blind spot (gc / nogc / index-based)

Every external tool surveyed instruments **malloc boundaries**. Simple has
FOUR allocator models, and three of them are invisible to malloc-level tools:

- **nogc malloc-backed** (rt_alloc): all tools apply. Covered today.
- **GC tier** (gc_async_mut): heaptrack/ASan see the GC's page requests, not
  object lifecycle. Needed: alloc/sweep hooks in the GC feeding the same
  counters (live-after-collect, reclaimed/collection, survivor attribution
  with owner tags that survive moves).
- **Index-based arenas/slotmaps** (AST arena, ECS stores, handle tables):
  the dominant model inside the compiler — and the source of the stage-4 bug
  class. ASan/GWP-ASan see one big block; a stale index is NOT a wild pointer.
  Equivalents live at the arena interface: slot-alloc/free as first-class
  events → attribution; generation checks (L6) → the UAF detector; slot
  poison + delayed index reuse → quarantine. This is infra we must build
  ourselves; no external tool provides it.
- **Static pools** (noalloc/baremetal): high-water + exhaustion metering only.

Design consequence: a single instrumentation trait (alloc/free/owner/bytes)
implemented by rt_alloc, the GC, every stdlib arena/slotmap, and pools — so
attr/harden/genarena reports are uniform across all four models. Captured in
`feature_backend_memory_infra_toggle.md` (tier × allocator-model section).

## 3c. GPU (CUDA/HIP) memory profiling + debugging (web, 2026-07)

Simple's gc_async_mut gpu/cuda/torch tier allocates device memory through
SFFI wrappers — one more choke point, same trait applies (owner-tagged
device-alloc/free events). External tools:

- **NVIDIA compute-sanitizer** (cuda toolkit): memcheck (OOB/misaligned +
  device leak check), racecheck (shared-mem races), initcheck (uninit device
  reads), synccheck. Works on ANY CUDA binary — ours included, zero
  integration. **ADOPT-as-docs** + `--mem-infra=gpu-sanitize` wrapper that
  execs through it (config-gated, off by default; it costs GPU memory + time).
- **PyTorch memory snapshot / memory_viz**: records every device alloc with
  stack + timeline, interactive web viewer, open snapshot format. The best
  UX in the space. **ADAPT-IDEA**: our device-alloc trace dumps in a
  memory_viz-compatible snapshot so we inherit their viewer for free.
- **CUPTI / NVML**: activity-record API for memory ops; NVML for device-level
  truth (the smaps_rollup analog). Feed `simple mem gpu` device rows. LOW.
- **cudaMallocAsync pools**: cuMemPoolGetAttribute exposes
  reserved/used/high-water per pool — free per-pool metering if the cuda
  tier allocates via pools. **ADOPT** (pool stats = arena metering on device).
- **ROCm/HIP**: rocprof (API/activity traces incl. memory), rocgdb
  (device-side watchpoints), omnitrace/rocprofiler-sdk timelines,
  AMD_LOG_MASK runtime logging. Same wrapper strategy, HIP lane.
- Device-side guard/canary sampling (GWP-ASan analog on GPU) exists nowhere
  mainstream — compute-sanitizer covers the class; do NOT hand-roll.

## 4. Recommendations (ranked, value per cost)

1. **Per-owner allocation attribution** (filed) — LOW cost, kills gap #1 for
   the common case; stack-sampling mode later.
2. **GWP-ASan-style sampled guard pages in `rt_alloc`** — LOW cost,
   backend-agnostic, catches UAF/overflow in ordinary runs (gap #4).
3. **Debug-tier hardened allocator** (Zig-GPA-style quarantine + poison) —
   LOW cost, gap #6, makes UAF deterministic instead of silent.
4. **`--mem-infra=` build interface with per-backend capability matrix**
   (filed) — makes ASan/MemProf one flag away on LLVM, degrades gracefully
   to runtime equivalents on Cranelift/interpreter (gap #4/#7 plumbing).
5. **Strict interpreter mode (Miri-lite)** — MED cost, gap #3, unique to us.
6. **Stdlib generational slotmap** — LOW-MED, generalizes L6 (stale-index
   class) to user code.
7. LLVM MemProf/PGHO, OxCaml-style modes, HWASan/MTE — WATCH/long-term.

## Sources

- https://llvm.org/docs/MemProf.html — MemProf/PGHO
- https://discourse.llvm.org/t/rfc-a-framework-for-allocator-partitioning-hints/87434 — PGHO allocator RFC (2025)
- https://llvm.org/docs/GwpAsan.html — GWP-ASan design
- https://arxiv.org/abs/2311.09394 — GWP-ASan paper
- https://blog.trailofbits.com/2025/12/16/use-gwp-asan-to-detect-exploits-in-production-environments/
- https://google.github.io/tcmalloc/gwp-asan.html — tcmalloc integration
- https://fil-c.org/ , https://fil-c.org/invisicaps , https://lwn.net/Articles/1042938/ — Fil-C/InvisiCaps
- https://vale.dev/memory-safe — Vale generational references
- https://github.com/koute/bytehound , https://github.com/kde/heaptrack — profilers
- https://blog.janestreet.com/oxidizing-ocaml-locality/ , https://dl.acm.org/doi/10.1145/3674642 — OxCaml modal memory management

## First dogfood profiles (2026-07-29)

Rust-seed driver (`src/compiler_rust/target/debug/simple`), `SIMPLE_MEM_ATTR=1`.

**Workload A** — `simple run src/app/memstat/main.spl --by-owner` (near-idle
baseline; `rt_mem_attr_report(32)` on itself):
| owner | live | peak | allocs |
|---|---|---|---|
| `<unattributed>` | 827-865 | 827-865 | 18 |
(only row; top-5 = 1 row total)

**Workload B** — wrapper script reading a real 485,397-byte `.spl` source
(`src/lib/nogc_sync_mut/js/engine/interpreter_native.spl`), tokenizing the
first 15,000 chars into 846 words / 457 unique into a `Dict`, then
`rt_mem_attr_report(20)` + `rt_heap_live_bytes_by_kind(1..28)`:
| owner | live | peak | allocs |
|---|---|---|---|
| `<unattributed>` | 540,968 | 540,968 | 1,131 |
(only row; top-5 = 1 row total)

Per-kind live bytes (Workload B; kinds not listed were 0):
| kind | bytes | count |
|---|---|---|
| 1 String | 540,969 | 1,129 |
| 2 Array | 96 | 3 |
| 3 Dict | 32 | 1 |

Observations:
1. **Owner attribution is currently blind for ordinary interpreted
   execution.** Both workloads dump 100% of live bytes into a single
   `<unattributed>` bucket — 827-865 B/18 allocs idle, 540,968 B/1,131 allocs
   under real work. `rt_mem_attr_set_owner` evidently isn't wired into common
   interpreter allocation sites (string slice, array push, dict insert); only
   explicitly-tagged call sites would ever show a named owner. As shipped,
   the owner table answers "how much is live" but not "who allocated it" for
   a typical compiler-ish run — exactly gap #1 already filed, now confirmed
   empirically rather than just in principle.
2. **Per-kind byte counts undercount container backing storage by orders of
   magnitude.** String (kind 1) is 99.98% of tracked bytes and looks
   accurate (dominated by the live 485 KB source-file string + its 15 KB
   slice). But Array holds only 96 B/3 objects despite an 846-element
   `words` array, and Dict holds only 32 B/1 object despite 457 live
   entries — container growth/bucket storage clearly isn't routed through
   the same kind-tagged path as boxed strings, so trusting Array/Dict rows
   to size "what's using memory" would be actively misleading.
3. **`rt_mem_attr_report_print` (heap.rs:777) is dead code** — no CLI
   subcommand calls it, so `simple compile <file>` (pure Rust-side
   parse/typecheck/codegen, no interpreted `.spl` in the loop) has *no* way
   to emit an owner/kind report at all; the infra is currently reachable
   only from inside interpreted `.spl` code via the `rt_mem_attr_report`
   extern. A real "measure the compiler compiling" workload needs either a
   CLI flag wiring that print, or the compile path itself moved behind an
   interpreted entry point.
