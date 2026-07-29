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
