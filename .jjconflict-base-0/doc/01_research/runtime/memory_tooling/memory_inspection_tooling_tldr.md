# Memory Inspection Tooling — TL;DR

**Date:** 2026-06-11

## Verdict

`gc_*` and `nogc_*` binaries are **byte-identical at runtime** — no GC exists.
"GC mode" = allocate-and-leak. The gc/nogc split is a directory convention + lint-only;
`gc_boundary_check` runs only at `bin/simple lint`, never at compile/test time.

## Three-Tier On/Off Architecture

```
+----------------------------------------------------------+
|  Tier 1: COMPILE-TIME (zero cost, always)                |
|  Transitive @nogc enforcement (D-style)                  |
|  extend noalloc_checker + gc_boundary_check              |
|  -> Hard error at compile time, not just lint            |
|  Overhead: 0 CPU / 0 memory / 0 at runtime              |
+----------------------------------------------------------+
         |
         v  (opt-in per build flavor)
+----------------------------------------------------------+
|  Tier 2: DEBUG / TEST BUILD FLAVOR (zero cost in prod)   |
|  mimalloc MI_DEBUG_FULL + memtrack/lsan wrappers         |
|  bin/simple test uses --debug-alloc by default           |
|  CI: ASan+LSan on C runtime (-fsanitize=address,leak)    |
|  Overhead ON: moderate (per-alloc fill + metadata)       |
|  Overhead OFF: literal zero (not in release binary)      |
+----------------------------------------------------------+
         |
         v  (always in release binary, env-toggleable)
+----------------------------------------------------------+
|  Tier 3: PRODUCTION SAMPLING (negligible)                |
|  mimalloc MI_GUARDED (GWP-ASan model)                   |
|  MIMALLOC_GUARDED_SAMPLE_RATE=4000 (default 1/4000)      |
|  Catches heap-OOB/UAF in production — Chrome/Android use |
|  Overhead ON: ~0-1% CPU, negligible memory               |
|  Overhead OFF: ~0% (one sampled branch/alloc)            |
+----------------------------------------------------------+
```

## Key Numbers

| Tier | CPU (on) | Memory (on) | Cost (off) |
|------|----------|-------------|------------|
| 1 Compile-time | 0 | 0 | 0 |
| 2 Debug flavor | moderate | per-alloc metadata | **0** |
| 2 CI ASan+LSan | ~2x | ~2–4x | **0** |
| 3 MI_GUARDED sampling | ~0–1% | small | ~0% |

## Prerequisite Gap

`gc_*` means **allocate-and-leak** today. A real GC, eager-free, refcount, or
explicit-arena decision must precede Tier 1 enforcement — otherwise the boundary
being enforced has no semantic counterpart on the `gc` side.

Full research: `doc/01_research/runtime/memory_tooling/memory_inspection_tooling.md`
