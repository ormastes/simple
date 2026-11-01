<!-- claude-research 2026-11-01, base origin/release/1.0.0 @ 4de6127c67d -->
# dir_tldr_aspect: Local Research

**Feature:** a directory-scoped TLDR ("dir TLDR") that every per-directory compile checks
first; an optional scheduler policy of one compile job per directory with the dir TLDR
resident; OOP aspects whose pointcuts drive a dynamic traversal plugin that weaves
functions; and reuse of one plugin instance across directories whose plugins differ only in
the directory path or matcher.

**Status:** research only. Nothing has been implemented. Requirements are pending user selection.

## 1. Key finding: most owners already exist

The repo already has a directory-level TLDR (`__init__.tld`) and per-directory pointcut
match shards. This feature should **extend existing owners**. It should not create a
parallel "dir manifest" or a second cache service.

| Concern | Existing owner | Citation |
|---|---|---|
| Directory TLDR (`__init__.tld`) | `PackageInitTldV1`: `parent_scope_digest`, `membership_root_digest`, `aspect_root_digest`, `trait/macro/extension/template_root_digest`, `initializer_contract_digest` | `src/compiler/00.common/cache_contract/package_init_tld_v1.spl:15-25`, validation `:41-47` |
| Per-directory join-point facts | `JoinPointFactV1`, `DirectoryJoinPointFactsV1`, `directory_facts_key_v1`, `directory_join_point_facts_guarded_v1` | `src/compiler/00.common/cache_contract/aspect_match_shard_v1.spl:33,41,164,180` |
| Pointcut selector (flat binary node array) | `PointcutSelNodeV1`, `PointcutSelectorV1`, `PointcutMatchShardV1`, `PointcutMatchCacheV1`, `WeavePlanDeltaV1` | `aspect_match_shard_v1.spl:51,58,68,84,95` |
| Driver: per-dir shard acquire, single flight | `AopMatchDriverStateV1`, `aop_selector_plan_acquire_v1`, `aop_directory_facts_from_hir_v1`, `aop_match_shard_acquire_v1` | `src/compiler/80.driver/cache/aop_match_cache_driver_v1.spl:44,107,139,186` |
| Prior plan for directory AOP | the "Directory generation requirement" and "Required directory traversal cache" sections | `doc/03_plan/compiler/cache/aop_directory_plan_cache_2026-10-30.md` |
| Combined AOP/macro/generic cache plan | | `doc/03_plan/compiler/cache/generic_aop_macro_semantic_cache_plan_2026-10-24.md` |
| File TLDR summary | `tldr_summary_path_v1`, `tldr_summary_entries_v1`, `tldr_summary_produce_v1` | `src/compiler/80.driver/cache/tldr_summary_v1.spl:40,87,182` |
| TLDR import routing | | `src/compiler/80.driver/driver_tldr_import_route_v1.spl`, `driver_unit_tldr_imports_v1.spl` |
| HIR surface from TLDR | | `src/compiler/20.hir/hir_lowering/module_surface_from_tldr_v1.spl`, `_Items/module_tldr_registration.spl`, `archive/tldr_function_header_v1.spl` |
| Generic TLDR view | `GENERIC_TLDR_VIEW_SCHEMA_V1`, facets `generic.signature/bound/body` | `src/compiler/00.common/cache_contract/generic_tldr_view_v1.spl:22,42-45`; projector `src/compiler/10.frontend/cache_artifact/generic_tldr_projector.spl` |
| Macro RR contract (#5736, #5739) | families definition-consumer/name-resolution/name-absence and subject prefixes | `src/compiler/00.common/cache_contract/macro_rr_contract_v1.spl:25-45`; `macro_reference_manifest_v1.spl`; projector `10.frontend/cache_artifact/macro_reference_projector.spl` |
| Generic RR facets (#5735 design, #5745 impl) | RR facets plus per-target object keys from HIR variants | `generic_tldr_view_v1.spl` facets; PR #5745 |
| RR shard and edge | `ReverseReferenceEdgeV1`, `ReverseReferenceShardV1`, `ReverseReferenceDeltaV1` | `src/compiler/00.common/cache_contract/reverse_reference_shard_v1.spl:18,26,32` |
| RR coordinator | `ChangedSemanticFacetV1`, `OldNewMembershipV1`, `VerifiedAffectedDomainV1`, `AffectedQueryPlanV1` | `src/compiler/80.driver/cache/reference/reverse_reference_coordinator_v1.spl:43,50,64,78` |
| Frontend AOP model | `PointcutKind`, `AdviceKind`, `JoinPointKind`, `Pointcut`, `glob_match` | `src/compiler/10.frontend/core/aop.spl:22,28,44,74,120` |
| Aspect registry (declare and claim) | `aspect_claim_key`, `aspect_registry_declare` | `src/compiler/10.frontend/aspect_registry.spl:118,146` |
| Aspect validation | `aspect_module_identity_index` | `src/compiler/35.semantics/aspect_validation.spl` |
| HIR forward weave (`aop_weave`) | `AspectForwardWeaveClaimV1`, `weave_forward_advice_claim_in_module_v1`, base-body store | `src/compiler/35.semantics/aspect_weave.spl:107,150,172-190` |
| MIR advice injection | `inject_before/after_success/after_error/around_advice`, `apply_weaving_result` | `src/compiler/50.mir/mir_aop_injection.spl:38,67,92,151,215` |
| Weaver hook | `fn aop_weaver() -> AopWeaver?` | `src/compiler/00.common/compilation_context.spl:195` |
| Built-in aspects (already OOP classes) | `LogAspect`, `TracingAspect`, `ContractAspect`, `install_*_aspect(weaver, aspect, pointcut)` | `src/plugins/aspects_builtin/log_aspect.spl:13,37`; `tracing_aspect.spl:12,23`; `contract_aspect.spl:12` |
| Plugin and backend receipts | | `src/compiler/00.common/backend_plugin/receipt.spl`; `00.common/dynamic_identity/closure.spl` |
| Per-file worker pool | `native_file_worker_pool_request_v1(requested, host_cpus)`, worker spec and batch | `src/compiler/80.driver/driver_build/native_file_worker_v1.spl:75,101,131`; incremental `native_file_worker_incremental_v1.spl` |
| Build scheduler | `SchedulerActionV1`, `plan_ready_actions_v1`; `plan_parent_graph_wave_v1` | `src/app/build/scheduler/planner.spl:4,52`; `parent_graph_wave_plan_v1.spl:56` |
| Single flight | `CacheSingleFlightV1` | `src/compiler/80.driver/cache/daemon/cache_single_flight_v1.spl` |
| Prior aspect research | | `doc/01_research/local/aspect_dynload.md`, `aspect_typed_facets.md`, `aspect_component_admission.md` |
| Incremental TLDR and SCV | | `doc/01_research/local/simple_compiler_incremental_build_tldr_scv_metadata_design_2026-10-08.md` |

## 2. Gaps relative to the user request

1. **Before-source check is not wired.** The 10-30 plan requires that a directory's admitted
   `__init__.tld` exist and validate before any source compile. Today
   `aop_directory_facts_from_hir_v1` (`aop_match_cache_driver_v1.spl:139`) recomputes facts
   from HIR on every compile, and the publication gate (`three_payload_generation_publisher_v1`)
   is closed. The native/Rust `CacheNamespaceAuthorityV3` providers are Unsupported.
2. **The scheduler has no directory unit.** `native_file_worker_pool_request_v1` sizes the pool
   by CPU count only (`:75-84`), and `SchedulerActionV1` (`planner.spl:4`) carries no
   directory grouping or residency affinity.
3. **Aspects are OOP only at runtime.** The `aspects_builtin` classes cover runtime advice. The
   compile-time weave is a free-function pipeline (`aspect_weave.spl`, `mir_aop_injection.spl`)
   with no trait for "pointcut → traversal → placement".
4. **No traversal plugin contract.** Matching produces `PointcutMatchShardV1.sorted_matching_ids`,
   and placement is hard-wired to the four inject_* forms.
5. **No plugin reuse identity.** `AopMatchDriverStateV1` interns selector *plans* by semantic
   digest (`:73-88`), but match results are deliberately directory-scoped (10-30 plan:
   "identical selectors do not make directory match results interchangeable"). Nothing
   normalises a plugin *instance* (code plus config) away from its dir path.

## 3. Constraints
- One process per file (parse→HIR→MIR→obj). A "per-dir job" is a job that keeps the dir
  TLDR resident and drives per-file pipelines in its own process (sequentially or on threads),
  or hands each file to a cc1-style child. It never splits phases across processes.
- HIR is target-neutral. The dir TLDR carries all cfg variants, and guards are already modelled
  by `active_guard_root_v1`.
- First `.o` within 10 s, so producing the dir TLDR must not gate the first file in big dirs.
- Memory: keep 24 GB free, one heavy build ≤64 GB, 80 jobs.
- The frozen stage2 must parse any `src/compiler` change, so add no new grammar. Use SDN and
  no nil or Any outside unsafe. Existing debt: `_dir_of` compares `rfind == nil`
  (`aop_match_cache_driver_v1.spl:122`).
