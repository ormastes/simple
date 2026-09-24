<!-- codex-design -->
# SPipe Plan: Kernel/Plugin Migration

Status: PLAN ONLY. KPM-REQ-010..013 remain blocked by user selection. Existing
dirty kernel-closure test work is evidence under review, not a completed phase.

## Shared scenario and checker names

Manual steps are exactly: `step("Classify the kernel and plugin closure")`,
`step("Negotiate the plugin interface")`, `step("Validate the versioned
parameter object")`, and `step("Compare kernel rebuild identities")`.

Checker helpers are exactly:

- `check_kernel_closure_partition`
- `check_iface_id_compatibility`
- `check_param_header_valid`
- `check_param_ext_policy`
- `check_plugin_negotiation_receipt`
- `check_plugin_manifest_identity`
- `check_kernel_rebuild_identity`
- `check_requires_range_resolution`
- `check_unsatisfied_range_lock_error`
- `check_mutation_red_result`

The shared type names are exactly `IfaceId`, `ParamHeader`, and `ParamExt`.
Unimplemented helpers must call `fail(...)`.

## Planned traceability

| Requirement | Planned evidence | State |
|---|---|---|
| KPM-REQ-001 | clean/illegal/empty closure fixtures and mutation-red checker | Existing work requires review |
| KPM-REQ-002..006 | ABI digest, param evolution, manifest, static/dynamic refusal fixtures | Planned |
| KPM-REQ-007/008 | table registration and P-edit/K0-edit bootstrap identity comparison | Planned |
| KPM-REQ-009 | injected defect must reverse each phase verdict | Planned |
| KPM-REQ-010..013 | selection-specific matrix | Pending user selection |
| KPM-REQ-014 | `test/01_unit/app/pkg/requires_range_spec.spl`: `simple lock` records satisfying `provides/requires` resolutions; an unsatisfied caret/tilde range fails with an attributed lock error | Planned after Phase 7; no backtracking solver |
| KPM-NFR-001..006 | startup timing, hot-path counters, receipts, bootstrap and mutation evidence | Planned |

Keep the phase-specific executable paths already named in
`doc/03_plan/compiler/plugin_arch/kernel_plugin_migration_plan.md`; do not add a
duplicate umbrella spec unless implementation proves the phase specs cannot
express the end-to-end contract. Generated manuals mirror those paths only
after executable specs exist and docgen reports zero stubs.
