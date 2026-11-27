# SIMPLE_STRICT_FIELD_FORWARDING opt-in is a workaround (RETIRED)

Bug id: `strict-field-forwarding-opt-in-20261027`. Date: 2026-10-27. Status: closed (2026-11-26).
Req: REQ-SELFHOST-ACCESSOR-001/002. Owner: compiler 20.hir lane.

## Resolution (2026-11-26)
- Audited `src/compiler` for undefined field reads on typed receivers and repaired the three remaining sites:
  - `src/compiler/90.tools/leak_check/types.spl` & `main.spl`: added `warn_threshold_kb`, `fail_threshold_kb`, `rss_budget_kb`, `sample_ms` to `LeakCheckConfig` and `max_rss_kb` to `LeakCheckResult` (fixing the 8 HIR strict-field-forwarding errors in `src/compiler/90.tools/leak_check/growth_runner.spl`).
  - `src/compiler/35.semantics/error_formatter.spl`: replaced `span.column` with `span.col` (matching `std.common.diagnostics.span.Span`).
  - `src/compiler/90.tools/stats/tag_classifier.spl`: replaced `item.file` with `item.file_path` (matching `DocItem` and `src/app/stats/tag_classifier.spl`).
- Removed `# @workaround bug=strict-field-forwarding-opt-in-20261027`, `_strict_field_forwarding_state`, `strict_field_forwarding_enabled`, `strict_field_forwarding_reset`, `env_get_opt("SIMPLE_STRICT_FIELD_FORWARDING")`, `warn_undefined_field`, and `accessor_warned_keys` from `src/compiler/20.hir/hir_lowering/_Expressions/accessor_forwarding.spl`, `types.spl`, and `context_helpers.spl`.
- `lower_accessor_read` now unconditionally emits the hard error `no field \`{name}\` on type and no get_/is_ accessor{hint}` with `accessor_suggestion` hints.
- Updated `accessor_forwarding_strict_opt_in_spec.spl`, `accessor_getter_forwarding_spec.spl`, `wa_src_lane3_workarounds_spec.spl`, `hir_lowering_begin_module_reset_and_traits_spec.spl`, and `scripts/check/census-undefined-field-reads.spl`.

## Historical Workaround (2026-10-27)
`src/compiler/20.hir/hir_lowering/_Expressions/accessor_forwarding.spl` previously kept the
undefined-field hard error behind `SIMPLE_STRICT_FIELD_FORWARDING=1`
(`# @workaround bug=strict-field-forwarding-opt-in-20261027 ...` on the state var),
emitting `[W-HIR-FIELD-001]` warnings by default until `src/compiler` was audited.

## Census (2026-10-27)
Method: one `simple run` process looping `parse_full_frontend` + `HirLowering.with_filename`
+ `lower_module` over each file, counting `W-HIR-FIELD-001` messages (~4 s per 30 files).
Sweep: 10.frontend 204 files, 20.hir 104, 50.mir 165, 80.driver first 200 of 454 = 673 files.
Result: 0 warnings in 0/673 files. Top offending names: none.
Caveat: **LOWER BOUND**, not a measurement of the whole compiler. Per-file lowering has no imported type tables, so reads on
imported owners have owner_id < 0 and are never checked; only same-file types are covered
(harness validated on a fixture: 2/2 warnings). A true count needs lowering with the full
module graph (driver path); not done in the light lane. Extrapolation from same-file
coverage: 0 / ~1570 compiler files, unproven for cross-file owners.

Next step: rerun the census with the full module graph (imported type tables) once the
phase-3 full CLI exists; use that count to size step 1 of the removal plan.

## Full Module-Graph Census (2026-11-27)
- Tooling update: extended `scripts/check/census-undefined-field-reads.spl` with `--lower-prefix`, `--shard`, Windows `/` path normalization, `/testdata/` exclusion, per-site deduplication, and `parse_module_source` error surfacing (`selftest` extended).
- Method: lowered all non-vendor/non-generated/non-testdata `.spl` modules across `src/{compiler,plugins,app,lib}` with `w2_census.exe` (strictly serial, 10 GB RSS / 120 s per-run caps) totaling **14,252 lowered files**:
  - `src/compiler` (**2,685 lowered** across `00..99`: `s1(00..30)=683`, `s2(35..60)=523`, `s3(70)=463`, `s4(80)=490`, `s5(90..99)=526`):
    - **3 findings already fixed upstream** on `release/1.0.0`: `src/compiler/20.hir/hir_lowering/_Items/module_tldr_registration.spl:111,119` (`admitted_function_abis`, fixed in `#12062` / `f7819267b6b`) and `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl:3691` (`local_map`, fixed in `9a9800b74f0`).
    - **5 + 4 JSON-twin findings fixed in this follow-up PR**: `src/compiler/90.tools/coupling/report.spl:83,158` (`inv.stable_module`/`unstable_module`/`stable_instability`/`unstable_instability` -> `from_module`/`to_module`/`from_instability`/`to_instability`) and `report.spl:95,167` (`LCOMResult.class_name` added and populated from `compute_lcom4(class_name, ...)` in `src/compiler/90.tools/coupling/lcom.spl`).
    - **9 findings fixed in this follow-up PR**: `src/compiler/90.tools/stats/tag_classifier.spl` (`DocItem` collided with `compiler/10.frontend/parser/doc_gen.spl`; introduced self-contained `StatsDocItem` in `src/compiler/90.tools/stats/types.spl`, re-exported from `stats/__init__.spl`).
    - **4 legacy unbraced-`export use` facade subtrees excluded**: `src/compiler/90.tools/{depgraph,fix,header_gen}`, `src/compiler/95.interp/interpreter/llvm`.
  - `src/plugins` (**106 lowered**): **0** findings.
  - `src/app` (**3,696 lowered**): **141** single-root findings in non-compiler app modules (`test_runner_new` dropped from 65 to 7 when cross-tree lowered with `src/lib/nogc_sync_mut/test_runner` [`74` files lowered], with remaining 7 in `src/app/test_runner_new/test_db_validation.spl` referencing `std.test_runner.test_db_core.TestDatabase`; other clusters in unintegrated `src/app/interpreter`, `dashboard*`, `wm_compare`, `svim/language_port.spl`, `vscode_extension/manifest_gen.spl`, `llm_dashboard/gui/mcp_panel_html.spl`, `cli/doc_coverage_command.spl`).
  - `src/lib` (**7,765 lowered**): **67** `no field` findings across unintegrated/stale modules (`src/lib/nogc_sync_mut/engine/{component,physics,render,scene}`, `src/lib/nogc_async_mut/engine/physics/simple/joints3d.spl`, `src/lib/nogc_sync_mut/replay/semantic/async_timeline.spl`, `src/lib/common/structural/placement/placement_types.spl`, `src/lib/gc_async_mut/gpu/browser_engine/gpu_web/layout/cuda_execution_port.spl`); **10** parse/empty-export-glob subtrees skipped (`linalg`, `ndarray`, `compositor`, `container`, `engine/input`, `fs/nvfs`, `simple_db_if`, `testing`, `kernel_plugin`, `tooling`), plus **1** OOM-capped leaf subtree (`src/lib/gc_async_mut/io`, >10 GB RSS cap) and `src/lib/nogc_sync_mut/io` top-level files skipped on >10 GB RSS cap (2 subdirs lowered).

- **DB reconciliation:** registered in bug_db.sdn (bugs_active + bugs) on 2026-10-27.
