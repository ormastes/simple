# TLDR: aspect weaving through TLDR (2026-11-28)

Full design: `aspect_tldr_async_trace.md`. Addendum to
`pseudo_immutable_cache_async_build_design.md`; base `origin/release/1.0.0` @ `3d3a74d786c`.
Sibling: `generic_instance_tldr_trace.md` (same engine, same reverse-reference machinery, same coverage gate).

- No weave pass. Matching and weaving are single-flight, set-once, content-keyed queries in the one scheduler; a file's compile task awaits them and weaves as stages of its own src -> obj pipeline.
- Facts travel in TLDR: `aspect-decl|` (family, advice id, selector, scope, order, signature/effects slot, body facet) and `join-point|` (`JoinPointFactV2` with signature and base body digests) per module; `__init__.tld` aggregates them (`aspect_root_digest` over interface digests, no body).
- Stage order: parse -> typed HIR -> await `effective_advice(dir)` -> plan over the file's own rows -> weave HIR -> MIR -> weave MIR -> obj. Nothing at or before typed HIR awaits an aspect slot; a file never awaits a sibling. A failed index slot is terminal: diagnostics still come out, no object is published.
- Woven unit = the file's one object, keyed by `hir_key + plan_digest`; an empty plan keeps today's key. The per-join-point weave key has the join point signature and no shard-wide input. Mir-family rules and the log config are coarse per-file key inputs.
- Persisted shards use the sha256 `pointcut_match_identity_v1`; the xxh3 key is an in-memory handle only.
- Invalidation: selector change -> old ∪ new matches; advice signature/effects/order -> woven units with that advice plus ABI consumers; advice body -> advice object + relink only (D1; woven objects rebuild only if the advice is inlined); no change -> zero aspect slots, zero weave, zero links.
- Cache hits replay the reverse-reference and trace rows stored with the artifact; a record without rows is a miss; a hit proves `plan_digest` from recorded plan inputs without running any match.
- Planner old side: a per-directory aspect plan receipt persisted beside the incremental manifest.
- Trace: fact rows only; "why" is a pure re-evaluation of the selector over one fact. Surfaces come from the one shared `TraceViewProjection` stage (extreme-typing lane).
- Census: 15 gaps with file:line in §2.2; production still runs two whole-program weave passes, a process-global registry and match state, an empty pointcut list to the planner, no `aop-consumer` rows and no async step.
- Gate: decision and condition coverage (95 % per unit module, 70 % over the set), function-entered check, Windows path normalisation, plus SSpec-as-document scan and `doc/06_spec` mirror.
- Stages: `doc/03_plan/compiler/aspect_cache/aspect_tldr_async_trace_plan.md`.
