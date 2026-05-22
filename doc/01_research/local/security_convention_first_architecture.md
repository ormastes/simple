<!-- codex-research -->
# Security Convention-First Architecture Local Research

Date: 2026-05-22

## Source Plan

Primary plan: `doc/plan/security_convention_first_architecture.md`.

The plan requires Simple security to infer architecture coordinates from the convention:

- `src/<layer>/<feature_group>/<feature_leaf>/...`
- `layer = first folder under src`
- `feature = remaining folder path`

It also requires default compile-time checks for:

- `SEC101` layer skipping.
- `SEC201` cross-feature access without a gate.
- `SEC301` scattered authorization outside security roots.
- `SEC401` ambient authority without explicit capability handles.

## Existing Implementation

Related implementation is concentrated in:

- `src/compiler_rust/compiler/src/security.rs`
- `src/compiler_rust/compiler/tests/security_policy_hir.rs`
- `src/compiler_rust/compiler/src/weaving.rs`
- `src/compiler_rust/runtime/src/security_runtime.rs`

Prior `security_mdsoc_dimension` work already provides:

- Security/gate/sandbox/capability parsing and HIR lowering.
- Gate inventory, access matrix, security AOP, sandbox, capability, and violations SDN generation.
- Compile-time AOP lowering into `SecurityAdvicePlan`.
- Runtime `rt_security_*` gate, policy, sandbox, and audit handlers.
- `SEC201`, `SEC301`, and `SEC401` checks using HIR facts where available and source fallback otherwise.
- Native registry startup for generated security AOP manifests.

## Current Delta Implemented

This pass added the first convention-first architecture slice:

- `infer_security_coordinate` now supports both legacy `src/feature/<feature>/<layer>` and convention-first `src/<layer>/<feature...>` paths.
- Layer-first paths infer dotted feature leaves, for example `src/service/user/profile/profile_service.spl` -> `layer=service`, `feature=user.profile`.
- Source and HIR import facts can now identify layer-first imports such as `use domain.user.profile.model`.
- `SEC101` is emitted when same-feature code skips more than one configured default layer, for example `ui -> domain`.
- `build_security_maps` now exposes `layer_map.sdn` and `feature_map.sdn` from the same convention inference.
- `simple security check` writes those map artifacts, and `simple security map` prints them directly.
- `build_security_gate_map` now exposes convention-derived gates from `src/security/gate/*.spl`, and `SEC201` can use those inferred gates as the required crossing for feature-group boundaries.

## Remaining Gaps

- Source/SDN merge with `configurable` and `final` policy relaxation rules is documented but not yet implemented for security policy.
- Generated artifacts do not yet include dedicated `ui_policy.sdn` or `report.md` outputs.
- Remote `SecurityContext`, permission snapshots, and UI policy DSL remain design-level.
- Sandbox manifest generation exists for declared sandboxes/gates, but backend lowering remains future work.
- Convention-first gate naming now handles `src/security/gate/user_admin.spl` -> `feature user` to `feature admin`; future work should broaden this into the full source/SDN policy merge.
