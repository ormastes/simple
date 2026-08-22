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
- CollectionPlan fusion precedes general MIR fusion.
- Profiles rank work but never prove semantics.
- CollectionPlan stays in existing `35.semantics`/`60.mir_opt` layers; no fake `40.collection_plan` or `65` layer.

Hot-path rules: one parse/typed artifact per revision; one CFG build per function revision; bounded caches/solvers; no warm-request full-tree scan/compiler subprocess; disabled profiling performs no allocation/I/O.

Start at:

- `doc/05_design/simple_compiler_performance_memory_efficiency.md`
- `doc/03_plan/agent_tasks/simple_compiler_performance_memory_efficiency.md`
- `doc/03_plan/sys_test/simple_compiler_performance_memory_efficiency.md`
