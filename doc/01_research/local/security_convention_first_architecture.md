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
- `SEC501` now flags source-level `thread_local SecurityContext` access inside async functions and requires task-local context or an explicit context parameter.
- The security inventory now carries `ui_policy.sdn` and `report.md`; `simple security check` writes those files and the planned `access_matrix.sdn` name while retaining `access_matrix.generated.sdn`.
- Source `allow` and `deny` security rules now carry `configurable` and `final` metadata through parser AST and HIR.
- `security_sdn_merge_violations_sdn` parses structured `security.allow` / `security.deny` SDN config with `simple_sdn` and reports `SEC601` when config weakens a final source deny rule, `SEC602` when config weakens a non-configurable source deny rule, and `SEC603` for malformed security SDN.
- `simple security check --config security.sdn` appends the source/SDN merge validation to `violations.sdn`.
- `ui_policy.sdn` now renders a permission snapshot manifest with display-only authority, server-gate-required semantics, policy-version requirement, stable observation keys, extracted conditions, and inferred scopes.
- First-class source `ui_policy` declarations now parse, lower into HIR, and render `show <key> when <condition>` rules into permission snapshot entries.
- Convention-first gate naming now handles `src/security/gate/user_admin.spl` -> `feature user` to `feature admin`.
- Minimal source `security:` policy blocks now work without a required policy name, and `layers ...` / `isolate ...` sugar lowers into layer and feature dimension rules.
- Security context propagation now includes explicit task-scoped helpers so async runtimes can isolate contexts by task id instead of treating thread-local state as authoritative.
- Async HTTP handler dispatch now reconstructs a server-side `SecurityContext` from safe request metadata and scopes it around content handler execution.
- Host scheduler polling now exposes scheduler-owned task identity, and HTTP dispatch allocates/enters scheduler task identity for reconstructed remote `SecurityContext` instead of keying security state by worker/fd.
- Sandbox inventory now emits backend-specific `sandbox_lowering.sdn` plans for Linux, WASI, Simple VM, baremetal, and Simple OS native object-capability handles.
- Remote HTTP dispatch now has an opt-in HMAC signed bearer token path that authenticates only validated session/user/capability claims and keeps unvalidated dispatch anonymous.
- Remote security lifecycle primitives now include key-id based signing key rotation, session lookup, refresh, and revocation before remote authority reconstruction.
- Hosted native security registry initialization now embeds sandbox lowering metadata and the runtime records backend IDs plus capability-handle counts when a generated sandbox is entered.
- Hosted runtime sandbox entry now activates lowered capability-handle policy so runtime-managed privileged APIs can reject ungranted capability IDs while a sandbox is active.
- Runtime fiber identity hooks now let future fiber schedulers enter/restore a current task id that participates in native `rt_current_task_id` selection for task-scoped `SecurityContext`.

## Remaining Gaps

- Remote `SecurityContext` transport/reconstruction has safe HTTP dispatch, HMAC token validation, local key-ring rotation, session lookup, refresh, and revocation; durable/distributed session storage and operational key rollout remain future work.
- Task-local context helpers, HostScheduler task identity, Rust cooperative async current-task-id exposure, FutureExecutor current-task-id exposure, fiber identity hooks, native `rt_current_task_id` selection across Rust runtime identities, and Simple `current_unified_task_key` selection exist.
- Sandbox manifest generation, backend lowering artifacts, hosted runtime registry installation, and hosted capability-handle enforcement exist for declared sandboxes/gates; concrete kernel/VM/backend syscall isolation remains future work.
