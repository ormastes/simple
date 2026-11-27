# TLDR: generic instance traceability through TLDR (2026-11-28)

Full design: `generic_instance_tldr_trace.md`. Addendum to
`pseudo_immutable_cache_async_build_design.md`; base `origin/release/1.0.0` @ `6b0b52f6f43`.

- Full monomorphization, fully async, no separate pass: `InstanceTask(key)` is a compile task in the same scheduler and `CompileInvoker` as `CompileTask(file)` (R01).
- Demand-driven: a task that meets `Template<Args>` requests it through the single-flight reader; one set-once slot per `ConcreteTldrKey` is the cross-module dedup.
- Provider: the template entry carries `body_digest` plus `open_needs` (instances its body requires as a function of its binders), a write-once slot filled by the typed-HIR stage.
- Consumer: each module's TLDR carries a `needed-instance|` section of direct needs `(ConcreteTldrKey, TemplateId, ArgsId, origins)`; only `Concrete` views enter it.
- Closure = async demand over direct needs + substituted `open_needs`; no body is opened to find instances. Instance set = slot table at scheduler quiescence, sorted by key. Depth 32 and a session budget bound it.
- An instance owns itself: one task, one object named by its key. Concrete view and HIR are target-neutral; MIR/object keys add target, toolchain and lane.
- Reverse refs (`generic-specialization`, existing family): body -> instances, signature/bound -> instances and consumer modules, instance -> requesters. A body edit rebuilds exactly that template's instance objects; consumer module objects stay.
- No-change build: zero instance tasks, zero links.
- Trace queries (who / why / from where / cost) read the section and RR rows; the `TraceViewProjection` surface is not implemented yet.
- Remote: an instance task is a content-keyed action; inputs are template entry, body section, argument keys, read TLDRs, target, toolchain. Local and remote objects must be byte-identical.
- Seed: syntactic only, stays erased, neither writes nor reads these sections (Q13 open).
- Not landed and needed first: async stage functions, `CompileInvoker`, key record v2, write-once slots, `.sphb`/`.spmb`, ledger, concrete-view acquisition, `40.mono` substitution. `generic_instance_prelink_v1.md` describes deleted code.
- Coverage: line % has no denominator in the seed's report; gate on per-file decision coverage (95 % unit, 70 % set) until line sites are registered.
- Stages: `doc/03_plan/language/type_system/no_any_inference_plan.md` S3-F1..F10; wave slots in `doc/03_plan/compiler/cache/pseudo_immutable_cache_impl_plan.md` §5.
