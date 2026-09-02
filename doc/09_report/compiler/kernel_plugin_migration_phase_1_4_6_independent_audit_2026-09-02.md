# Kernel Plugin Migration Phases 1–4 and 6 — Independent Audit

Date: 2026-09-02

## Verdict

| Phase | Verdict | Reason |
|---|---|---|
| 1 | **PASS (code), BLOCKED (runtime)** | Typed HIR now owns a canonical semantic ABI extractor. Both clean streaming and non-streaming production HIR paths compute and log the digest without using it for admission or build decisions. |
| 2 | **PASS (code), BLOCKED (runtime)** | `ParamHeader`/`ParamExt` and typed `AspectParamsV1` are honest. Enforcement now parses AST declarations/calls and the evolution gate compares real `Vn` to same-version and `Vn+1` schemas. |
| 3 | **PASS (code), BLOCKED (runtime)** | SMF writing is deterministic; parsing uses the SDN parser, exact headers/types/row widths, duplicate rejection, and checked load. ABI/interface refusal now returns named errors rather than silently interpreting. Package dependency identity fields reject wrong shapes. |
| 4 | **PASS (code), BLOCKED (runtime)** | The production callable table remains active. The host contract digest is canonical, each provider derives a distinct digest from that contract and its rule identity, and dispatch independently recomputes both identities before calling a row. |
| 6 | **PASS (code), BLOCKED (runtime)** | APK/SFFI refusal behavior remains intact. Native cache identity no longer defaults or selects ABI policy: it requires an explicit policy plus an admitted Stage-2 receipt bound to the running compiler and runtime ABI, otherwise it mints an uncacheable identity. |

## Authoritative Evidence

- Typed-HIR ABI extraction: `src/compiler/20.hir/abi_interface.spl:308`, `src/compiler/20.hir/abi_interface.spl:350`. Production compute-and-log callers: `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:410`, `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:884`.
- Typed params: `src/lib/common/plugin/iface_id.spl:9`, `src/lib/common/plugin/aspect_params.spl:12`, `src/compiler/90.tools/lint/param_object_rules.spl:36`, `scripts/check/check_param_object_evolution.spl:49`.
- Canonical/fail-closed manifests: `src/compiler/80.driver/watcher/smf_manifest.spl:355`, `src/compiler/80.driver/watcher/smf_manifest.spl:375`, `src/compiler/80.driver/driver_api_interpret.spl:40`, `src/compiler/80.driver/driver_api_interpret.spl:54`.
- Production lint call: `src/compiler/90.tools/lint/_LintMain/lint_checks.spl:285`, `src/compiler/90.tools/lint/_LintMain/lint_checks.spl:429`. Canonical host/provider identities and independent dispatch checks: `src/compiler/90.tools/lint/lint_rule_api.spl:65`, `src/compiler/90.tools/lint/lint_rule_api.spl:77`, `src/compiler/90.tools/lint/static_rules.spl:44`, `src/compiler/90.tools/lint/static_rules.spl:60`.
- APK/SFFI: `src/lib/common/aspect_pack.spl:1819`, `src/lib/common/aspect_pack.spl:2218`, `src/lib/nogc_sync_mut/sffi/dynamic_versioned.spl:211`, `src/lib/nogc_sync_mut/sffi/dynamic_versioned.spl:295`.
- Explicit ABI admission: `src/compiler/80.driver/driver_build/incremental.spl:292`, `src/compiler/80.driver/driver_build/incremental.spl:353`, `scripts/bootstrap/bootstrap-from-scratch.sh:2581`, `scripts/bootstrap/bootstrap-from-scratch.sh:2948`. No policy label overrides runtime ABI values.

## Runtime Rows

| Row | Status | Evidence |
|---|---|---|
| Focused Simple unit/SPipe specs | **BLOCKED** | The admitted Stage-2 binary returns `unknown command 'check'`. The deployed seed's `check` reaches an unrelated existing `always_inline` semantic error before these rows; it is not authoritative evidence. A separate bootstrap remains live and was not restarted or modified. |
| Param evolution self-test | **BLOCKED** | Requires a runnable Simple source entrypoint. `sh -n scripts/check/check-param-object-evolution.shs` passes. |
| Source whitespace/patch integrity | **PASS** | Focused `git diff --check` passes. |
| Real SFFI unload-marker scenarios | **BLOCKED** | Fixture is real C/dylib evidence, but executing its Simple spec requires the unavailable test runner. No synthetic receipt is accepted. |

## Files Changed by This Audit

- `scripts/check/check-param-object-evolution.shs`
- `scripts/check/check_param_object_evolution.spl`
- `src/compiler/00.common/assurance/package_pins.spl`
- `src/compiler/70.backend/backend_plugin/loader.spl`
- `src/compiler/80.driver/driver_api_interpret.spl`
- `src/compiler/80.driver/watcher/__init__.spl`
- `src/compiler/80.driver/watcher/smf_manifest.spl`
- `src/compiler/90.tools/lint/param_object_rules.spl`
- `src/compiler/99.loader/module_loader_compat.spl`
- `src/lib/common/aspect_pack.spl`
- `src/lib/common/plugin/instrumentation_aspect_pack.spl`
- `src/lib/common/plugin/negotiation.spl`
- `src/lib/nogc_sync_mut/sffi/dynamic_versioned.spl`
- `test/01_unit/compiler/assurance/package_pins_spec.spl`
- `test/01_unit/compiler/backend_plugin/dynamic_loader_spec.spl`
- `test/01_unit/compiler/driver/interface_digest_wiring_spec.spl`
- `test/01_unit/compiler/driver/smf_manifest_gate_spec.spl`
- `test/01_unit/compiler/loader/aspect_pack_smf_section_wiring_spec.spl`
- `test/01_unit/compiler/plugin_arch/param_object_lint_spec.spl`
- `test/01_unit/lib/aspect_pack/negotiate_spec.spl`
- `test/01_unit/lib/common/plugin/negotiation_spec.spl`
- `test/01_unit/lib/sffi/dynamic_versioned_negotiate_spec.spl`
- `doc/09_report/compiler/kernel_plugin_migration_phase_1_4_6_independent_audit_2026-09-02.md`

Unrelated dirty files and concurrent bootstrap/policy edits were preserved.

## Follow-up Remediation Files

- `scripts/bootstrap/bootstrap-from-scratch.sh`
- `src/compiler/00.common/cache/canonical_identity.spl`
- `src/compiler/20.hir/abi_interface.spl`
- `src/compiler/35.semantics/interface/compile_interface.spl`
- `src/compiler/80.driver/cache/action_key.spl`
- `src/compiler/80.driver/driver_build/incremental.spl`
- `src/compiler/80.driver/driver_hir_pipeline_lowering.spl`
- `src/compiler/90.tools/lint/lint_rule_api.spl`
- `src/compiler/90.tools/lint/static_rules.spl`
- `src/compiler/90.tools/lint/rules/accessor_parent_name_rule.spl`
- `src/compiler/90.tools/lint/rules/bare_primitive_internal_rule.spl`
- `src/compiler/90.tools/lint/rules/const_ref_default_rule.spl`
- `src/compiler/90.tools/lint/rules/cow_alias_hotpath_rule.spl`
- `src/compiler/90.tools/lint/rules/leading_operator_rule.spl`
- `src/compiler/90.tools/lint/rules/module_init_literal_rule.spl`
- `src/compiler/90.tools/lint/rules/nonexistent_type_rule.spl`
- `src/compiler/90.tools/lint/rules/os_freestanding_rule.spl`
- `src/compiler/90.tools/lint/rules/param_object_rule.spl`
- `src/compiler/90.tools/lint/rules/param_tag_rule.spl`
- `src/compiler/90.tools/lint/rules/raw_sffi_rule.spl`
- `src/compiler/90.tools/lint/rules/riscv_debuggability_rule.spl`
- `src/compiler/90.tools/lint/rules/silent_default_rule.spl`
- `src/compiler/90.tools/lint/rules/unwrapped_foreign_resource_rule.spl`
- `test/01_unit/compiler/driver/native_cache_producer_identity_spec.spl`
- `test/01_unit/compiler/interface_compat/compile_interface_spec.spl`
- `test/01_unit/compiler/lint/lint_rule_table_spec.spl`
- `doc/09_report/compiler/kernel_plugin_migration_phase_1_4_6_independent_audit_2026-09-02.md`
