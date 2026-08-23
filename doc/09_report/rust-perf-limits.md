# Architecture-level performance and memory limits

**This is the single canonical place to record perf/memory limits that cannot be
fixed within the "minimal, semantics-preserving edit" constraint.** Other lanes:
please **append a row here** rather than starting a parallel report.

Purpose: the project's hard rule is *do not hurt the feature set or the design to
hit a number*. This file is the escape valve. Anything that cannot be fixed
without changing architecture or dropping capability is recorded here — with the
measured number, the architectural reason, what would have to be sacrificed, and
the estimated saving if it ever were — instead of being forced through or
silently skipped.

- Owner lane: worker-memory (`/mnt/fast/wt-workermem-1`)
- Opened: 2026-08-23

## Standing targets

| phase | target | current measured | status |
|---|---|---|---|
| compile (per worker) | **< 1 GB** | 2.40-2.74 GB RSS, VmPeak 3.37 GB | **not met** — see L1, L2, L3 |
| link | **< 3 GB** | not yet measured as RSS; link is 93% of back-end wall (56.5 s of 60 s) | **unmeasured** — see L6 |

Progress against the compile target so far: the slim parse-shard entry
(`504a57d11c8`) took a parse-shard child from 3.82 GB to 1.54 GB, which is within
~50% of the 1 GB target for *that* phase. HIR shard children still spawn the full
worker and remain at 2.4-2.7 GB. The remaining gap is L1-L3 below, and none of
the three is reachable by a local edit.

## Recording format

Each limit: measured number → architectural reason → what capability or design
property would have to be sacrificed → estimated saving.

---

## L1 — Process-per-worker shares nothing: `Pss ≈ Rss`, 14 MB shared across 8 workers

- **Measured.** `smaps_rollup` of a live `native_build_worker`: `RssAnon`
  2,516,200 kB = **99.4% of RSS**; `RssFile` 14,164 kB; `Shared_Clean` 14,160 kB;
  `Pss` 2,516,752 kB ≈ `Rss` 2,530,364 kB. The 14 MB shared is the `simple`
  binary's text and nothing else.
- **Architectural reason.** Shard children are `spawn` + `exec`, so each one
  re-materialises the identical compiler closure as **private dirty heap**. All
  N workers parse the same closure and read the same immutable source and cache
  files, but every byte of that is rebuilt per process. The cost of N workers is
  therefore exactly N × a full private heap, with no sublinear term at all.
- **What would have to be sacrificed.** Either (a) fork the orchestrator *after*
  the closure is built, so COW shares it — this changes the process model and
  requires the interpreter to be fork-safe (allocator state, open fds, any
  background thread), or (b) mmap read-only source/cache pages and intern
  strings in a shared segment, which means source text stops being an owned
  `text` value and becomes a borrowed view — a direct hit to value semantics.
  Both are design changes, not minimal edits.
- **Estimated saving.** The closure load is the dominant fixed term (~3.3 GB
  before the slim-entry fix, ~0.9-1.5 GB after). Under (a), N workers would cost
  roughly `closure + N × per-shard-working-set` instead of `N × closure`. At 8
  workers that is on the order of **10-18 GB saved per build**. It is also the
  only known route to the < 1 GB compile target for the HIR phase.
- **Status.** Filed, not implemented. Overlaps the sibling frozen-surface cache
  lane (audit §3 items 2 and 7).

## L2 — RSS is monotone: 2.40 → 2.74 GB, never released; one 2,450 MB mimalloc arena

- **Measured.** 521 samples / 10 s interval / ~9 min across 41 live workers:
  every worker climbed 2.40 → 2.74 GB and **none fell**. Largest single mapping
  is `[anon:mimalloc]` at **2,450.7 MB**; next is the binary at 13.5 MB. Swap 0.
  `VmPeak` 3.37 GB > `VmHWM` 2.41 GB.
- **Architectural reason.** Two independent causes, and it matters that they are
  separate. (i) **Retention**: several structures are process-immortal by design
  — SoA retained source text for *every* closure file
  (`driver_source_pipeline_loading.spl:318-347`), `ctx.sources` boxed
  `SourceFile` records duplicating those same fields
  (`parsing.spl:421-433`, a second full inventory), frozen
  `ModuleSurfacesByName` (`parsing.spl:447-486`), and the flat AST arena /
  token interner whose `ast_reset()` reallocates but never shrinks
  (`parsing.spl:226-258`). (ii) **Allocator**: mimalloc does not return the
  arena, so even freed memory stays resident as RSS.
- **What would have to be sacrificed.** For (i), frozen module surfaces being
  process-immortal is the property that makes the surface lane correct and
  fast; making them droppable means re-deriving them, i.e. giving back the
  caching the design exists to provide. Making `SourceFile` borrow indices into
  the SoA owner instead of copying removes one of two live copies of every
  file's text but changes those records from owned values to views. For (ii),
  `MIMALLOC_PURGE_DELAY` / `mi_option_purge_decommits` is a *tunable*, not a
  design change, and is the one tractable piece here — but purging costs CPU and
  must be measured before adoption, and should be scoped to worker children only.
- **Estimated saving.** Removing the duplicate `ctx.sources` inventory (audit §3
  item 5) is worth roughly one full copy of all closure source text. Allocator
  purge would convert the monotone climb into a sawtooth; the ~0.34 GB observed
  climb is the floor of what it could return, likely more. Neither alone reaches
  < 1 GB; both plus L1 might.
- **Status.** The allocator tunable is a live follow-up for this lane. The
  retention half is design-level and filed.

## L3 — Full entry-closure source text is loaded and retained in *every* worker

- **Measured / located.** `compile_targets.spl:968-978, 1001-1011`;
  `loading.spl:318-347`.
- **Architectural reason.** The shard work queue is a flock'd **dynamic** queue
  (`driver_source_pipeline_parsing.spl:133-196`) — a shard may claim *any*
  module, so ownership is not known at load time. A static per-shard filter is
  therefore not merely an optimisation, it is incorrect. Relatedly, the
  streaming surface path has no shard-ownership check inside the loop at all
  (`parsing.spl:333-420`; the check lives at `:584`, the exit at `:486`), so
  every worker parses and surfaces every source.
- **What would have to be sacrificed.** Either lazy per-module load (a real
  change to the load pipeline's contract, since text is currently guaranteed
  present), or a static shard split — which would give back the dynamic queue
  that removed the slow-slice tail. mmap-instead-of-retain is the third option
  and lands back in L1's value-semantics problem.
- **Estimated saving.** One full copy of closure source text per worker, times N.

## L4 — `--threads` had no `MemAvailable` clamp and no backoff — **FIXED**

Recorded here for completeness because it was the *lethal* one; the fix is in
`doc/08_tracking/bug/shard_threads_no_memavailable_clamp_2026-08-23.md`.

- **Measured.** Default `host_cpus/2` = 16 on this 32-core box ⇒ ~40 GB asked for
  by one run. run17 was OOM-reaped 3× (`rc=255` after 12,643 s, death points HIR
  13/688, 288/688, 509/688) at ~16 GB free; run18 likewise.
- **Fixed by** clamping the chosen count to
  `floor(MemAvailable × 0.6 / per-worker budget)`, per phase. This is *not*
  architectural: sharding is a cache warm-up, output is identical at any N, so
  lowering N is semantics-preserving by construction.
- **Measured effect** at `MemAvailable = 21,958,928 kB`, request 16: parse
  16 → 7 (26 → 11.6 GB), HIR 16 → 4 (48 → 12 GB).
- **Residual limit that stays here:** the clamp bounds the *damage*, it does not
  reduce per-worker cost. On a box with little free memory it will drive N to 1,
  trading wall time for survival. Removing that trade-off requires L1.

## L5 — Fixed startup does not shrink with N

- **Measured.** Closure load ~16-26 s and ~3.3 GB (~0.9-1.5 GB post-slim-entry),
  paid in full by every worker.
- **Architectural reason.** `wall ≈ fixed_startup + parse_work / N`, and
  `fixed_startup` is per-process. Beyond the point where `parse_work / N` is
  comparable to `fixed_startup`, extra workers buy almost no wall time while
  costing a full heap each. This is why 16 workers is worse than 6 on *both*
  axes, not a memory-vs-speed trade.
- **Saving.** Same fix as L1 (fork-after-closure); no independent one.

## L6 — Link is 93% of back-end wall

- **Measured.** 56.5 s of 60 s of back-end wall, per the MIR/codegen audit.
- **Status.** Link-phase **RSS is not yet measured**, so the < 3 GB link target
  is currently unverified in either direction. Flagged rather than guessed.
  Whoever measures it: append the number here.

## L7 — Interpreter family is ~92k LOC in the seed, larger than its own codegen

- **Measured.** `doc/01_research/compiler/dual_impl_test_sharing_assessment_2026-08-23.md`.
- **Relevance.** Every worker process loads it. It is a floor on the closure size
  that L1 and L5 are both fighting, and it cannot be trimmed without dropping the
  dual (interpret + compile) execution capability the design deliberately keeps.
