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

REQ-022: Remote `SecurityContext` lifecycle support shall provide key-id based signing key rotation, server-side session lookup, refresh, and revocation primitives for validating remote bearer tokens before reconstructing authority.

REQ-023: Hosted runtime sandbox entry shall activate lowered capability-handle policy so runtime-managed privileged APIs can reject ambient capability use that is not granted to the active sandbox.

REQ-024: Future fiber runtimes shall have an explicit current-task identity bridge that participates in the unified runtime task selector used by task-scoped `SecurityContext`.

REQ-025: SimpleOS kernel capability management shall install generated `sandbox_lowering.sdn` capability handles as pledged per-task `CapabilitySet` records so syscall capability checks deny ungranted authority.

REQ-026: Remote `SecurityContext` lifecycle state shall support SDN export/import for signing key rings and session stores, distributed merge of later session refreshes and revocations, and explicit key retirement for operational rollout.

REQ-027: Simple VM host-import filtering shall enforce active `sandbox_lowering.sdn` capability classes before interpreter extern dispatch, deny unmapped host imports by default under `simple_vm_capability_table`, and preserve explicit `rt_security_*` control-plane imports.

REQ-028: The Linux sandbox backend shall provide an installable seccomp-BPF profile that sets `no_new_privs` and can deny network and process-spawn syscall classes in the current process after host setup.

REQ-029: The Linux sandbox backend shall provide an installable Landlock filesystem ruleset that detects the kernel ABI, filters filesystem access rights by ABI version, grants configured read/write path-beneath rules, sets `no_new_privs`, and restricts the current process.

REQ-030: The WASI runtime shall support an explicit capability table that can be populated from lowered sandbox manifests and shall deny undeclared environment variables and preopened directories when the table is attached.

REQ-031: Baremetal sandbox lowering shall emit deterministic MPU/linker metadata, baremetal linker scripts shall keep the generated static capability/MPU sections with start/end symbols, and kernel sandbox install shall fail closed when baremetal lowering is present without the static section.

REQ-032: Remote `SecurityContext` validation shall expose hosted adapter seams for replicated session storage and opaque key rollout providers, and HTTP dispatch shall support validating v2 remote tokens through those adapters without requiring raw signing keys in request handling.

REQ-033: RISC-V baremetal sandbox support shall convert generated `pmp_region|base|size|permissions|locked` lowering metadata into concrete `pmpaddrN` and `pmpcfgN` CSR write plans, including NAPOT address encoding and locked read/write/execute PMP config bytes.

REQ-034: Hosted remote `SecurityContext` session storage shall provide a concrete Redis-backed deployment store using the existing Redis client, preserve the SDN session row format, use Redis TTLs for active expiry, and write revoked sessions as bounded tombstones instead of deleting them.

REQ-035: Hosted remote `SecurityContext` session storage shall provide concrete quorum behavior over replicated session adapters, including configurable read/write quorum counts, topology export, revocation-wins merge semantics, and latest-active-expiry merge semantics.

## Deferred Requirements

DEF-001: Specific KMS/HSM vendor clients remain future work beyond the hosted adapter seams, Redis session deployment store, quorum session-store behavior, SDN persistence, merge, rotation, and retirement primitives.

DEF-002: Non-RISC-V MPU backends and boot-time CSR/MMIO apply hooks remain future work beyond deterministic linker-section metadata, fail-closed static-section installation, hosted runtime checks, WASI env/preopen capability-table enforcement, Linux Landlock/seccomp filters, Simple VM host-import filtering, SimpleOS kernel capability installation, and RISC-V PMP CSR write-plan generation.
