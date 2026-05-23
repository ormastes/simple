<!-- codex-design -->
# Security Convention-First Architecture System Test Plan

## Scope

This slice is compiler diagnostic behavior, covered by Rust compiler tests rather than SPipe app specs.

## Coverage

- REQ-001: `infers_security_coordinates_from_layer_first_folders`.
- REQ-002: existing `infers_security_coordinates_from_feature_folders`.
- REQ-003: `reports_sec101_for_layer_skip_in_layer_first_layout`.
- REQ-004: `allows_adjacent_layer_access_in_layer_first_layout`.
- REQ-005: existing `SEC201` tests in `security_policy_hir.rs`.
- REQ-006: tests call `source_security_violations_sdn` without requiring a source security block.
- REQ-007: `renders_convention_first_layer_and_feature_maps`.
- REQ-008: `infers_gate_boundaries_from_security_gate_filename` and `sec201_uses_convention_gate_filename_as_required_crossing`.
- REQ-009: `infers_gate_boundaries_from_security_gate_filename`.
- REQ-010: `reports_sec501_for_thread_local_security_context_in_async_function`.
- REQ-011: `renders_ui_policy_and_report_artifacts`; driver `check` writes `access_matrix.sdn`, `ui_policy.sdn`, and `report.md`.
- REQ-012: parser test `parses_security_policy_configurable_and_final_markers`; HIR tests `records_security_rule_configurable_and_final_metadata`, `reports_sdn_override_that_weakens_final_source_policy`, `reports_sdn_override_that_weakens_non_configurable_source_policy`, `allows_sdn_override_for_configurable_source_policy`, and `reports_malformed_security_sdn_merge_config`.
- REQ-013: `renders_ui_policy_and_report_artifacts` and `renders_permission_snapshot_entries_for_ui_can_observations`.

## Verification Command

`cd src/compiler_rust && cargo test -p simple-parser --test security_policy --quiet && cargo test -p simple-compiler --test security_policy_hir --quiet`
