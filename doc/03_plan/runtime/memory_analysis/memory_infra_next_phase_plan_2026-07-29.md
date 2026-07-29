# Memory-infra next phase plan (2026-07-29)

Successor to the stage4 lanes plan (L1-L7 complete). Research:
`doc/01_research/runtime/memory_analysis/memory_infra_gap_and_tools_2026-07-29.md`.
Features: `doc/02_requirements/runtime/memory_analysis/feature_per_owner_allocation_attribution.md`,
`feature_backend_memory_infra_toggle.md`.

Cross-cutting requirement (all phases): every mechanism covers the four
allocator models — malloc-backed nogc, GC tier, index-based arenas/slotmaps,
static pools — via one instrumentation trait (alloc/free/owner/bytes). A
malloc-only implementation is an incomplete lane, not a done lane.

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

## WATCH (not scheduled)
LLVM PGHO feed-back once the allocator grows partitioning hooks; HWASan/MTE
on aarch64 boards; OxCaml-style local/unique modes as the long-term static
direction; Fil-C capability ideas.

## Verification culture
Each milestone lands with: fixture-backed spec (SSpec), overhead measurement
(warm run, before/after), and a one-page entry appended to the research doc.
