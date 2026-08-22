# Tests and Documentation Inventory

Scope: static inventory for `simple_compiler_performance_memory_efficiency` at
`37bd406e219cc35cae049b4130f5167c21801864`. No compiler, test, or benchmark
was executed. Vendored/runtime third-party sources are excluded.

## Authoritative inputs already present

- Audit: `doc/01_research/local/simple_compiler_performance_memory_efficiency_audit.md`.
- Optimizer requirements: `doc/02_requirements/feature/unified_optimizer_plugin.md`,
  `doc/02_requirements/compiler/optimization/simd_auto_application.md`,
  `doc/02_requirements/compiler/optimization/simd_fixed_and_scalable_vectors.md`,
  `doc/02_requirements/feature/perf_profile_reporting.md`, and matching NFRs.
- Related roadmap options (not selected requirements):
  `doc/02_requirements/language/options/simple_optimization_architecture_roadmap_2026-06-01_options.md`
  and `doc/02_requirements/nfr/simple_optimization_architecture_roadmap_2026-06-01_options.md`.
- Architecture: `doc/04_architecture/compiler/perf/compiler_optimization_infra_refactor_2026-05-13.md`,
  `doc/04_architecture/compiler/perf/simple_optimization_plugin.md`,
  `doc/04_architecture/compiler/simd/simd_auto_application.md`,
  `doc/04_architecture/compiler/simd/simd_unified_architecture.md`,
  `doc/04_architecture/language/memory_model_implementation.md`, and
  `doc/04_architecture/app/compiler/pure_simple_profile_guided_executable_optimization_2026-06-01.md`.
- User guides: `doc/07_guide/compiler/optimization/compiler_optimization_levels.md`,
  `doc/07_guide/compiler/optimization/compiler_optimization_plugin.md`,
  `doc/07_guide/compiler/optimization/compiler_simd_auto_application.md`,
  `doc/07_guide/compiler/check_perf.md`, and `doc/07_guide/app/lint.md`.
- Current implementation surfaces: `src/compiler/60.mir_opt/optimization_passes.spl`,
  `src/compiler/60.mir_opt/optimizer_manifest.spl`,
  `src/compiler/60.mir_opt/mir_opt_integration.spl`, and
  `src/compiler/60.mir_opt/mir_opt/{dce,const_fold,copy_prop,cse,gvn,loop_detect,loop_licm,loop_opt,bounds_check_elim,auto_vectorize,collection_opt,collection_opt_core,string_builder_opt,tco,typed_byte_canon,outline}.spl`.
- Lint tests identify the current collection/performance entry points:
  `test/01_unit/compiler/semantics/collection_patterns_lint_spec.spl`,
  `test/01_unit/compiler/lint/collection_easy_fix_spec.spl`,
  `test/01_unit/compiler/lint/collection_array_rebuild_spec.spl`,
  `test/01_unit/compiler/lint/collection_index_mutation_spec.spl`,
  `test/01_unit/compiler/lint/simd_opportunity_lint_spec.spl`, and
  `test/01_unit/compiler/lint/lint_profile_spec.spl`.
- MIR optimizer tests: `test/01_unit/compiler/mir_opt/pass_descriptor_spec.spl`,
  `dead_code_spec.spl`, `constant_folding_spec.spl`, `copy_propagation_spec.spl`,
  `strength_reduction_spec.spl`, `loop_invariant_motion_spec.spl`,
  `bounds_check_elim_spec.spl`, `auto_vectorize_spec.spl`,
  `collection_opt_spec.spl`, and `typed_byte_canon_spec.spl` in that directory;
  broader legacy coverage is under `test/01_unit/compiler/{complete,deep}/`.
- Performance evidence: `test/perf/compiler_perf_baseline_spec.spl`,
  `test/perf/compiler_runtime.spl`, `test/perf/collections/`,
  `test/01_unit/compiler/mir/mir_opt_benchmark_spec.spl`, and
  `scripts/check/check-perf-regression-tests.shs`.
- Relevant tracked defects/TODOs:
  `doc/08_tracking/todo/optimizer_manifest_dynamic_pass_routing_2026-08-18.md`,
  `doc/08_tracking/bug/backend_optimization_facts_gating_not_enforced_2026-07-20.md`,
  `doc/08_tracking/bug/optimizer_cli_warning_flood_2026-06-27.md`,
  `doc/08_tracking/bug/pure_simple_collection_perf_parity_gap_2026-05-14.md`,
  `doc/08_tracking/bug/lint_single_file_superlinear_timeout_on_line_count_2026-08-06.md`,
  `doc/08_tracking/bug/robust_lint_lane_scan_latency_2026-08-21.md`,
  `doc/08_tracking/bug/memory_retention_compiler_and_interpreter_2026-08-21.md`,
  `doc/08_tracking/bug/stage3_frontend_hir_unbounded_memory_growth_2026-08-10.md`,
  and `doc/08_tracking/bug/value_semantics_cow_alias_perf_class_2026-08-21.md`.
- Expert routing: `doc/00_llm_process/feature_expert/compiler_hardening/skill.md`,
  `doc/00_llm_process/feature_expert/memory_infra/skill.md`,
  `doc/00_llm_process/layer_expert/compiler_driver/skill.md`, and
  `doc/00_llm_process/layer_expert/mission_critical_memory/skill.md`.

## Material gaps

1. No selected feature/NFR pair exists for this audit. The new requirements
   must not silently inherit unselected roadmap options.
2. No single architecture/detail-design document defines `PerfFacts`, pass
   status/expectation, analysis preservation/invalidation, diagnostic policy,
   or the four-tier cost budget.
3. No system SSpec/manual pair traces the proposed COMP-PERF, LOOP, COLL009-018,
   and MEM diagnostics end-to-end through CLI profiles and exit status.
4. Existing pass unit specs do not by themselves prove canonical dispatch,
   effective-pipeline inclusion, a positive transform sentinel, semantic
   differential equivalence, or identity-wrapper CI rejection.
5. No shared adversarial matrix covers dominance, zero-trip loops, aliasing,
   trapping/exception paths, signed overflow, FP semantics, unsafe pointers,
   and irreducible CFGs for every activated transform.
6. Performance specs are dispersed and do not establish the proposed marginal
   compile/lint overhead, representative request latency, or max RSS budgets.
7. Escape tests exist (`test/01_unit/compiler/deep/analysis_escape_{1,2,3}_spec.spl`)
   but no evidence ties `NoEscape` to proof reasons, unknown-call fail-closed
   behavior, allocation thresholds, or heap-vs-promoted GC/lifetime parity.
8. Generated/manual spec documentation for this feature does not exist.

## Proposed requirement-to-test mapping

| Proposed requirement | Primary executable evidence | Additional evidence |
|---|---|---|
| REQ-001 Pass registry is truthful (`Active`, `AnalysisOnly`, `RemarkOnly`, `Skeleton`, `Disabled`) | extend `pass_descriptor_spec.spl`; new `optimizer_activation_integrity_spec.spl` | effective-pipeline JSON/text golden; COMP-PERF001 negative fixture |
| REQ-002 Every active transform reaches canonical dispatch and changes a sentinel | per-pass MIR specs plus new aggregate dispatch spec | before/after MIR structural diff and transformation count |
| REQ-003 Activated transforms preserve semantics | new differential system spec over interpreter/native supported rows | positive, negative, idempotence, malformed CFG, overflow/FP/trap/alias matrix |
| REQ-004 Shared cached CFG/dominator/loop/def-use/MemorySSA-lite facts are authoritative | focused unit specs for each fact and invalidation | counters prove one construction per valid cache epoch |
| REQ-005 Performance lint reuses frontend artifacts and remains bounded | extend lint profile/performance specs | `check-lint-cost-budget.shs`, wall time and max-RSS receipt on fixed corpus |
| REQ-006 COLL009-018 and LOOP rules have precise positive and suppression behavior | new table-driven lint unit specs | CLI system spec for profile/severity/exit/JSON output |
| REQ-007 MEM001-022 rules report multiplicity, uncertainty, and safe fix policy | new memory-efficiency lint unit specs | fix round-trip specs only for semantics-preserving fixes |
| REQ-008 Auto transforms require legality and profitability; misses are remarks | LICM/BCE/vector/collection specs plus missed-remark cases | profile hotness and reason-code golden |
| REQ-009 Escape analysis fails closed and explains proof/escape paths | extend `analysis_escape_*` | heap/promoted differential lifetime and GC-root test |
| REQ-010 Complexity regression compares a canonical baseline without false certification | new bounded program-analysis system spec | incomplete-analysis receipt must be non-PASS in Robust/Critical |
| REQ-011 Diagnostics are stable, structured, deduplicated, and profile-aware | lint CLI JSON/SDN/text system spec | warning-flood regression fixture and deterministic ordering |
| REQ-012 Compile-time and runtime resource targets are measured once on realistic fixtures | compiler baseline + collection benchmarks | recorded command, compiler hash, fixture hash, warm latency, peak RSS |

## Likely authoritative verification commands

Run each unchanged green gate at most once, after designs select exact files:

```sh
bin/simple test test/01_unit/compiler/mir_opt/<focused>_spec.spl --mode=interpreter
bin/simple test test/01_unit/compiler/lint/<focused>_spec.spl --mode=interpreter
bin/simple test test/01_unit/compiler/deep/analysis_escape_1_spec.spl --mode=interpreter
bin/simple test test/03_system/app/compiler/feature/simple_compiler_performance_memory_efficiency_spec.spl --mode=interpreter
bin/simple lint <changed-.spl-files>
bin/simple duplicate-check src/compiler/60.mir_opt --mode token --min-lines 5
bin/simple check src/compiler
bin/simple check src/lib
sh scripts/check/check-lint-cost-budget.shs
sh scripts/check/check-perf-regression-tests.shs
sh scripts/audit/direct-env-runtime-guard.shs --working
sh scripts/audit/direct-env-runtime-guard.shs --staged
```

Before release, also require the repository-wide SPipe/verify gates and confirm
`doc/06_spec` contains no executable `*_spec.spl`; generated manuals belong
there as Markdown only. Benchmark claims require a fresh recorded run and must
not be inferred from this static inventory.
