# TLDR — pseudo-immutable cache implementation plan

- Full plan: `pseudo_immutable_cache_impl_plan.md`; design: `doc/05_design/compiler/cache/pseudo_immutable_cache_async_build_design.md`.
- Bug first: HIR cache key (`80.driver/driver_hir_cache.spl:157`) has no target, while the parser strips cfg arms per target ⇒ cross-target HIR reuse. C1 folds the target in; C5 makes HIR target-neutral via `50.mir/mir_cfg_select.spl`.
- Then C2: xxh3 is a lookup hint only; persistent/untrusted hits need a crypto digest. C3: no truncated-hash identity.
- Then no-change build: N1 skip when the final artifact's receipt matches, N2 materialize when the destination is missing.
- Then structure: write-once slots (C4), shared fiber/process invoker + TestRunner on the scheduler (S1), compact IDs (S2), fused source→OBJ default (S3).
- Reuse: single-flight #4372, cache limits #4506, link receipts #4356, hash registry #4421, packed AST #4391-#4445.
