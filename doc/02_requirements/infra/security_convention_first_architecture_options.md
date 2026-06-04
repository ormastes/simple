<!-- codex-research -->
# Security Convention-First Architecture Feature Options

## Option A: Diagnostics-First Convention Enforcement

Description: Implement convention-first path inference and compile-time diagnostics before deeper runtime features.

Pros: Low risk, aligns with existing `security.rs`, immediately catches architecture violations, preserves zero-config defaults.

Cons: Does not finish remote context, UI policy, SDN merge, or backend sandbox lowering.

Effort: M, 2-4 files.

## Option B: Full Policy Artifact Generation

Description: Add `layer_map.sdn`, `feature_map.sdn`, `gate_map.sdn`, `ui_policy.sdn`, and `report.md` generation.

Pros: Makes the security graph more inspectable and LLM/tool-friendly.

Cons: Requires CLI/build output decisions and may expose unstable artifact schema.

Effort: L, 4-8 files.

## Option C: Source + SDN Merge

Description: Implement source policy plus SDN profile merge with `configurable` and `final` relaxation rules.

Pros: Directly supports deployment/profile override safety.

Cons: Requires SDN parser/schema decisions and careful conflict diagnostics.

Effort: L, 5-10 files.

## Option D: Remote/UI Policy System

Description: Add remote `SecurityContext`, permission snapshots, and UI policy DSL.

Pros: Addresses client/server authorization split.

Cons: Broadest scope; depends on policy graph stability and runtime/app integrations.

Effort: XL, 10+ files.
