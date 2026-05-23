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

## Verification Command

`cd src/compiler_rust && cargo test -p simple-compiler --test security_policy_hir --quiet`
