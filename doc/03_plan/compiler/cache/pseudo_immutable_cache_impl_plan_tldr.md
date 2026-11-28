# TLDR — pseudo-immutable cache implementation plan

- Full plan: `pseudo_immutable_cache_impl_plan.md`; design: `doc/05_design/compiler/cache/pseudo_immutable_cache_async_build_design.md`.
- Bug first: HIR cache key (`80.driver/driver_hir_cache.spl:157`) has no target, while the parser strips cfg arms per target ⇒ cross-target HIR reuse. C1 folds the target in; C5 makes HIR target-neutral via `50.mir/mir_cfg_select.spl`.
- Then C2: xxh3 is a lookup hint only; persistent/untrusted hits need a crypto digest. C3: no truncated-hash identity.
- Then no-change build: N1 skip when the final artifact's receipt matches, N2 materialize when the destination is missing.
- Then structure: write-once slots (C4), shared fiber/process invoker + TestRunner on the scheduler (S1), compact IDs (S2), fused source→OBJ default (S3).
- Reuse: single-flight #4372, cache limits #4506, link receipts #4356, hash registry #4421, packed AST #4391-#4445.
- Generic instances (§5, added 2026-11-28): specialization runs as async tasks on this engine, no separate pass. Stages `S3-F0`..`F10` live in `doc/03_plan/language/type_system/no_any_inference_plan.md`; design `doc/05_design/compiler/cache/generic_instance_tldr_trace.md`. Engine first: design §19 steps S1-1, S1-2, S1-3, S1-5, S2-1 gate the first instance object; early start is F0, F1, F2, F6 (early half), F10. `.spmb` has no owning step yet.
