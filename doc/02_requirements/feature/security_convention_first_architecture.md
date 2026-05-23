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

REQ-013: Generated `ui_policy.sdn` shall describe client permission snapshots as display-only hints, include stable observation keys and conditions, require a policy version, and state that server gates remain authoritative.

REQ-014: Source files shall support first-class `ui_policy` declarations whose `show <key> when <condition>` rules lower into `ui_policy.sdn` permission snapshot entries without requiring annotation-only discovery.

REQ-015: Source security policy grammar shall accept the convention-first minimal form `security:` with `layers ...` and `isolate ...` sugar, lowering it into layer and feature dimension rules.

REQ-016: Security context propagation shall expose explicit task-scoped context helpers so async code can isolate request identity by task id without relying on thread-local state as the semantic model.

REQ-017: HTTP transport dispatch shall reconstruct a server-side `SecurityContext` from safe request metadata and scope it around handler execution, while keeping unauthenticated remote requests anonymous and server-authoritative.

REQ-018: The security inventory shall emit a backend-specific `sandbox_lowering.sdn` artifact that maps abstract sandbox policies to concrete enforcement plans for Linux Landlock/seccomp/namespaces, WASI, Simple VM, baremetal MPU/linker regions, and Simple OS native object-capability handles.

REQ-019: Remote HTTP security context reconstruction shall support opt-in HMAC-signed bearer token validation, require session-token agreement, reject malformed/tampered/expired tokens, and keep the default unvalidated dispatch path anonymous.

REQ-020: Hosted native builds shall embed generated `sandbox_lowering.sdn` metadata into the runtime security registry, and the runtime shall retain sandbox backend and capability-handle metadata for observational backend installation checks.

REQ-021: HTTP handler dispatch shall route reconstructed remote `SecurityContext` through scheduler-owned task identity rather than worker/fd identity, including scheduler polling scopes and HTTP request handler scopes.

## Deferred Requirements

DEF-001: Remote `SecurityContext` key rotation, persistent session lookup, refresh flows, and distributed revocation remain future work beyond HMAC token validation.

DEF-002: Runtime installation and kernel/VM enforcement of lowered sandbox plans remains future work beyond generated backend lowering artifacts.

DEF-003: Unified task identity selection across HostScheduler, FutureExecutor, Rust cooperative async, and future fiber runtimes remains future work beyond exposing each runtime's current-task id.
