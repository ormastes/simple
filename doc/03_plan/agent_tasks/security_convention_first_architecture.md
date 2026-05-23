<!-- codex-design -->
# Security Convention-First Architecture Agent Tasks

## Completed This Slice

- Explorer agent: plan/docs gap analysis.
- Explorer agent: compiler implementation gap analysis.
- Main agent: implement convention-first coordinate inference and `SEC101`.
- Main agent: implement generated `layer_map.sdn` and `feature_map.sdn` plus `simple security map`.
- Main agent: implement generated `gate_map.sdn` and convention-derived gate boundaries from `src/security/gate/*.spl`.
- Main agent: implement `SEC501` for `thread_local SecurityContext` use in async functions.
- Main agent: add `ui_policy.sdn`, `report.md`, `access_matrix.sdn`, `simple security ui-policy`, and `simple security audit`.
- Main agent: implement source security `configurable` / `final` metadata and structured SDN merge validation.
- Main agent: extend `ui_policy.sdn` into a display-only permission snapshot manifest with stable observation keys and server-gate-required semantics.
- Main agent: implement first-class source `ui_policy` declarations for permission snapshot rules.
- Main agent: implement minimal `security:` grammar with `layers ...` and `isolate ...` convention sugar.
- Main agent: implement explicit task-scoped `SecurityContext` propagation helpers.
- Main agent: implement async HTTP handler dispatch scoping for reconstructed remote `SecurityContext`.
- Main agent: add focused compiler tests.

## Next Candidate Tasks

- Integrate remote `SecurityContext` transport/reconstruction with real client/server transports.
- Lower sandbox manifests to concrete backends.
