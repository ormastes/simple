# TLDR: aspect weaving through TLDR (2026-11-28)

Full design: `aspect_tldr_async_trace.md`. Addendum to
`pseudo_immutable_cache_async_build_design.md`; base `origin/release/1.0.0` @ `df04c6a4e7d`.
Sibling: `generic_instance_tldr_trace.md` (same engine, same reverse-reference machinery, same coverage gate).

- No weave pass. Matching and weaving are single-flight, set-once, content-keyed queries in the one scheduler; a file's compile task awaits them and weaves as a stage of its own src -> obj pipeline.
- Facts travel in TLDR: `aspect-decl|` (advice id, selector, scope, order, signature/effects slot, body facet) and `join-point|` per module; `__init__.tld` aggregates them (`aspect_root_digest`, `parent_scope_digest`, inline join-point table, all existing fields).
- Pull, not push: `advice_index(scope)` (Merkle over directories) -> `effective_advice(dir)` -> `match(selector, dir)` -> `weave_plan(file)`. No task reads another file's HIR or a global registry.
- Woven unit = the file's one object, keyed by `hir_key + plan_digest`; an empty plan keeps today's key. Weave always starts from the immutable base body.
- Invalidation: selector change -> old ∪ new matches (unweave, weave, reuse intersection); advice signature/effects/order -> woven units with that advice plus ABI consumers; advice body -> match sets reused and only the advice object rebuilds + relink (D1; woven objects rebuild only if the advice is inlined); no change -> zero match tasks, zero weave, zero links.
- Reverse references: existing `aop-consumer` family gets its first real producers.
- Trace: which advice applies where comes from the rows; "why" is a pure re-evaluation of the selector over one join-point fact. `TraceViewProjection` is built once, in shared stage TV-1 (D3).
- Census: shards, facts, apply key, old/new delta and the planner are landed as pure code; production still runs two whole-program weave passes, uses a process-global registry and match state, passes an empty pointcut list to the planner, writes no `aop-consumer` rows and has no async step. 14 gaps with file:line in §2.2.
- Engine: fact sections, selector unification, explain, plan digest, planner input and the coverage gate start now; async match needs S1-3/S1-5, weave stage needs S1-1/S1-2/S2-1, packed artifacts need S2-6/S3-1/S3-4/S3-5, zero reweave needs B-1..B-3.
- Coverage: the seed report has no line denominator; gate on decision and condition coverage (95 % per unit module, 70 % over the set) plus a function-entered check, with Windows path normalisation.
- Stages: `doc/03_plan/compiler/aspect_cache/aspect_tldr_async_trace_plan.md` AW-0..AW-12.
