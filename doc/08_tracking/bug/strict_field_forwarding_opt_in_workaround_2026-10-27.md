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

- **DB reconciliation:** registered in bug_db.sdn (bugs_active + bugs) on 2026-10-27.
