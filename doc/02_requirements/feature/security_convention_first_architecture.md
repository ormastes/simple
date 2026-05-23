<!-- codex-research -->
# Security Convention-First Architecture Requirements

Selected path: Option A, based on the active implementation request and `doc/plan/security_convention_first_architecture.md`.

## Requirements

REQ-001: The compiler shall infer security coordinates from convention-first paths of the form `src/<layer>/<feature...>/<file>.spl`.

REQ-002: The compiler shall preserve compatibility with existing `src/feature/<feature>/<layer>` security coordinate inference.

REQ-003: The compiler shall emit `SEC101` when same-feature access skips default layers by convention, for example `ui -> domain`.

REQ-004: The compiler shall allow adjacent same-feature layer access by default.

REQ-005: The compiler shall continue to emit `SEC201` for cross-feature access without a security gate.

REQ-006: The implementation shall keep convention-first security zero-config: no security block is required for default layer inference.

REQ-007: The security CLI shall expose generated `layer_map.sdn` and `feature_map.sdn` artifacts from convention-first inference.

REQ-008: The compiler shall infer gate boundaries from `src/security/gate/<from>_<to>.spl` when a gate omits explicit `from` and `to` clauses.

REQ-009: The security CLI shall expose generated `gate_map.sdn` artifacts.

REQ-010: The compiler shall emit `SEC501` when an async function uses `thread_local SecurityContext`; code must use task-local context or pass an explicit context parameter.

REQ-011: The security CLI `check` command shall emit the planned generated artifact set, including `access_matrix.sdn`, `ui_policy.sdn`, and `report.md`.

REQ-012: Source security policy rules shall support `configurable` and `final` metadata; SDN config may relax source deny rules only when the source rule is configurable, and shall report violations for final or non-configurable weakening.

## Deferred Requirements

DEF-001: Remote `SecurityContext` and permission snapshots remain future work.

DEF-002: Backend sandbox lowering remains future work beyond manifest generation.
