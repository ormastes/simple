<!-- codex-architecture -->
# Simple Compiler Performance/Memory Architecture — TLDR

Purpose: make optimizer claims truthful, share frontend/MIR facts, add precise performance diagnostics, and remove measured compiler/tool hot-path waste without unsafe speculative rewrites.

Core structure:

```text
CompilationRevision -> typed HIR collector -> diagnostics + CollectionPlan
                   -> MIR -> PerfFacts -> transforms + remarks
                                      -> PerfSummary/.sperf -> .sprof-v2
```

Decisions:

- `PassStatus` and `PassExpectation` are separate; only active passes transform.
- Unsafe active vector rewriting is contained first.
- `PerfFacts` is revision-bound, cached, immutable, and explicitly invalidated.
- Unknown alias/effect/range/escape/cost evidence rejects transforms.
- Source warnings, optimizer remarks, and compiler-integrity failures are distinct.
- Performance severity uses explicit evidence tiers; source/parsed/incomplete findings
  stay advisory, while only typed-proven facts may escalate to errors.
- CollectionPlan fusion precedes general MIR fusion.
- Profiles rank work but never prove semantics.
- CollectionPlan stays in existing `35.semantics`/`60.mir_opt` layers; no fake `40.collection_plan` or `65` layer.

Hot-path rules: one parse/typed artifact per revision; metadata-only severity projection;
one CFG build per function revision; bounded caches/solvers; no warm-request full-tree
scan/compiler subprocess; disabled profiling performs no allocation/I/O.

Bootstrap Stage 3 destination-owner decision (2026-08-26):

- Streaming HIR construction writes directly into `HirExprOutput`,
  `HirBlockOutput`, and `BootstrapHirFunctionOutput` through `_into` APIs.
  By-value compatibility wrappers remain available but stay off production.
- Explicit `Return` and assignment forms remain statements. The compiler must
  not rewrite a complex expression tail into `Return` merely to avoid an
  aggregate return boundary.
- The path remains O(N) time and O(depth) transient space, with one function
  owner plus geometrically grown reusable composite-depth slots; disabled
  routing and scalar tails add no allocations. Aggregate-boundary finalization
  must continue through owner-index MIR.
- Cycle 15 proved the direct simple-tail path (`native_build_help`: `has=true`,
  `stmts=0`) but crashed before publication of the later composite-tail
  `native_build_entry_from_args`. Repeated malformed-span receipts make a
  pre-publication composite boundary the strongest inference, not a proven
  fault location.

Start at:

- `doc/05_design/simple_compiler_performance_memory_efficiency.md`
- `doc/03_plan/agent_tasks/simple_compiler_performance_memory_efficiency.md`
- `doc/03_plan/sys_test/simple_compiler_performance_memory_efficiency.md`
