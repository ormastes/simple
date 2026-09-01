<!-- codex-research -->
# Aspect Dynamic Loading: NFR Options

**Status:** awaiting user selection; proposed targets are not current
measurements and are not final requirements.  
**Date:** 2026-08-20  
**Provenance:** highest-capability Codex audit session
`/root/audit_aspect_plan_completion`; lower-model sidecars: **N/A**.  
**Gate:** performance acceptance requires an admitted native Stage-4 binary;
interpreter or error-path results may diagnose behavior but cannot satisfy it.

Select one target profile below. Values are ceilings unless marked as a floor.

## NFR-A — Relative regression guardrails

- No-aspect cold-process startup: aspect-capable build p95 no more than **1.05x**
  and **3 ms** slower than the same admitted build with aspect registration
  disabled.
- Resident `try_facet` hit: p95 no more than **1.50x** a direct pre-resolved
  table lookup; advice dispatch p95 no more than **1.25x** an equivalent direct
  indirect call.
- Successful first-use acquisition: at least **500 MiB/s** admitted payload
  throughput after fixed overhead, with p95 fixed overhead at most **5 ms**.
- Peak RSS: no-aspect delta at most **8 MiB**; loaded-pack delta at most
  **1.25x** admitted uncompressed bytes plus **8 MiB** index/runtime overhead.
- After operational seal: **zero** loader filesystem opens/reads, decompression,
  mappings, relocations, or blocking activation waits.

**Pros:** portable across machines and compiler maturity; directly detects
regression; aligns with current comparative Class-A methodology.  
**Cons:** a slow baseline can pass; ratios become noisy for sub-microsecond hot
paths; less useful as an end-user promise.  
**Effort:** **M**, roughly 4–8 benchmark/evidence files plus native deployment.

## NFR-B — Balanced desktop/server absolute budgets

- No-aspect cold-process startup: p50 **≤ 20 ms**, p95 **≤ 30 ms**; enabling
  dormant aspect support adds p95 **≤ 2 ms**.
- Resident `try_facet` hit: p50 **≤ 500 ns**, p95 **≤ 1 us**. Published advice
  slot dispatch adds p50 **≤ 20 ns**, p95 **≤ 50 ns** over the control call.
- One successful first use of a 1 MiB pack: p50 **≤ 3 ms**, p95 **≤ 5 ms** with
  warm host page cache, including verify/decode/map/relocate/publish.
- Peak RSS: no-aspect delta **≤ 6 MiB**; one 1 MiB admitted pack **≤ 12 MiB**
  incremental `VmHWM`; cache metadata **≤ 64 bytes per exported binding** plus
  **2 MiB** fixed overhead.
- After operational seal: **zero** loader I/O and allocation on resident probe
  or advice dispatch; p99 waiter count and queue depth must return to zero after
  activation.

**Pros:** clear product promise; catches absolute startup and memory bloat;
separates first use from hot path.  
**Cons:** host-sensitive; may be unrealistic until bootstrap/compiler
performance is repaired; requires stable benchmark hardware class.  
**Effort:** **L**, roughly 8–14 benchmark/evidence/CI files.

## NFR-C — Mission-critical preload profile

- Startup preload fixture: **10 facets / 10 MiB** admitted uncompressed content
  reaches sealed operational state at p95 **≤ 100 ms** on the named reference
  host; no-aspect startup p95 remains **≤ 30 ms**.
- After seal, resident facet hit p99 **≤ 500 ns** and advice dispatch incremental
  p99 **≤ 30 ns**; p99-minus-p50 jitter **≤ 100 ns** over 10 million calls.
- After seal: **zero** filesystem access, mapping, decompression, relocation,
  allocation, locks, waits, retries, or generation changes on protected paths.
- Peak RSS after preload **≤ 32 MiB + 1.20x** admitted uncompressed bytes; RSS
  must not grow by more than **1 MiB** during 10 million protected calls.
- Pack unload/update is disabled after seal; any missing binding fails during
  preload, before operational entry.

**Pros:** falsifiable resident/realtime contract; bounded late-path behavior;
failures occur before mission operation.  
**Cons:** highest startup/RSS commitment; excludes hot update; nanosecond tails
need isolated hardware and careful instrumentation.  
**Effort:** **XL**, roughly 12–20 evidence/harness/platform files plus native
concurrency and syscall tracing.

## NFR-D — Staged evidence profile

Stage 1 is a release blocker now; Stage 2 becomes binding after the first
admitted success baseline.

**Stage 1:**

- Restore exact-source Stage-2 and obtain admitted Stage-3/Stage-4 receipts.
- Preserve the existing Class-A comparison ceilings: Simple versus C startup
  p50 and p95 **≤ 2.0x**, max RSS **≤ 4.0x** on the same fixture.
- Aspect-off versus disabled startup p95 **≤ 1.10x** and **≤ 5 ms** absolute
  delta; peak RSS delta **≤ 16 MiB**.
- Successful 1 MiB first use p95 **≤ 10 ms**; resident hit **≤ 10 us** p95.

**Stage 2:**

- Tighten aspect-off startup to **≤ 1.05x / 3 ms**, first use to **≤ 5 ms**,
  resident hit to **≤ 2 us**, and peak RSS to **≤ 8 MiB + 1.25x** admitted
  bytes, without changing semantics.
- Post-seal loader I/O remains **zero** in both stages.

**Pros:** achievable while bootstrap is unstable; makes evidence provenance a
first-class gate; avoids claiming unmeasured nanosecond performance.  
**Cons:** permits a temporarily weak product target; requires a scheduled
tightening milestone; Stage-1 values are unsuitable as final marketing claims.  
**Effort:** **M–L**, roughly 6–12 evidence/receipt/benchmark files plus bootstrap
repair owned outside this requirements artifact.

## Common measurement protocol (applies to every option)

1. Record exact executable SHA-256, source revision/tree identity, compiler
   stage receipt, host CPU/kernel, fixture digest, and feature flags.
2. Startup: use a fresh process per sample, warm host page cache unless a
   separate cold-cache result is labeled, at least **5 warmups + 30 measured
   runs**, and report p50/p95/max plus raw machine-readable samples.
3. Hot path: run at least **10 million** iterations after publication, include a
   matched control loop, subtract/report harness overhead, and report
   p50/p95/p99 rather than only an average.
4. First use: time the entire successful
   verify/decode/map/relocate/publish path. Report payload size and compression
   ratio. Error or `APK_MODULE_CORRUPT` paths do not count.
5. RSS: record Linux `/proc/<pid>/status` `VmHWM` and component attribution from
   `smaps_rollup` where available. Use an idle named reference host/container
   with fixed limits.
6. No-I/O: trace open/read/pread/mmap and runtime facade counters across at least
   **1 million** post-seal acquisitions/dispatches. Any loader-side event fails.
7. Concurrency: native threads/tasks start behind a barrier; at least **64
   callers × 100 repetitions** must demonstrate one successful activation, the
   same published generation, deterministic failure fan-out, and no stranded
   waiters. Inline interpreter execution is correctness-only evidence.
8. One independent highest-capability review must validate receipt freshness,
   absence of stubs/fallback binaries, scenario quality, and target calculation.

## User selection requested

Choose NFR-A, B, C, or D and name the reference host class. If choosing D, also
select the milestone that makes Stage 2 mandatory. No final
`doc/02_requirements/nfr/aspect_dynload.md` should be created before that choice.

