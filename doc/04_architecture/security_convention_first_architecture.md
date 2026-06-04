<!-- codex-architecture -->
# Security Convention-First Architecture

## Status

Accepted for the implemented convention-first compiler and runtime security slice. This document covers `REQ-001` through `REQ-037`, `REQ-LKMS-CI-001` through `REQ-LKMS-CI-008`, and the NFRs in `doc/02_requirements/nfr/security_convention_first_architecture.md`.

## Context

Simple treats security as an architecture-level compile-time concern. Source layout, security grammar, generated SDN manifests, runtime context propagation, and sandbox backends all feed one security inventory instead of relying on scattered runtime checks.

The convention-first model is:

```text
src/<layer>/<feature...>/<file>.spl
```

The compiler infers `layer` from the first path segment after `src` and infers `feature` from the remaining directory path. The legacy layout remains supported:

```text
src/feature/<feature>/<layer>/<file>.spl
```

## Layer List

The default convention-first layer order is:

```text
ui -> api -> service -> domain -> port -> infra -> driver -> kernel
```

Security-owned roots are separate from normal feature descent:

- `src/security/gate`: cross-feature gates and gate boundary inference.
- `src/security/policy`: source policy rules, `configurable` and `final` metadata, and SDN merge authority.
- `src/security/sandbox`: abstract sandbox declarations lowered into backend plans.
- `src/security/ui_policy`: display-only permission snapshot declarations.

## Current-State Map

Compiler security owns inference, diagnostics, inventory, and generated artifacts:

- `src/compiler_rust/compiler/src/security.rs`: coordinate inference, feature/layer graphing, `SEC101`, `SEC201`, `SEC501`, security maps, security inventory, and SDN rendering.
- `src/compiler_rust/compiler/tests/security_policy_hir.rs`: HIR security inventory, diagnostics, policy merge, UI policy, sandbox lowering, and backend lowering coverage.
- `src/compiler_rust/driver/src/cli/security.rs`: `simple security` CLI map, audit, UI policy, and generated artifact exposure.
- `src/compiler_rust/driver/src/cli/check.rs`: `check` artifact writing path for `access_matrix.sdn`, `layer_map.sdn`, `feature_map.sdn`, `gate_map.sdn`, `ui_policy.sdn`, `sandbox_lowering.sdn`, and `report.md`.

Runtime security owns task context, remote context validation, lifecycle, and enforcement:

- `src/lib/nogc_sync_mut/security/types.spl`: shared security context, token, key, session, sandbox, and capability data.
- `src/lib/nogc_sync_mut/security/auth/context_propagation.spl`: explicit task-scoped security context helpers.
- `src/lib/nogc_sync_mut/security/auth/rotation.spl`: key rotation and retirement helpers.
- `src/lib/nogc_sync_mut/security/remote_redis.spl`: Redis-backed session persistence and bounded revocation tombstones.
- `src/lib/nogc_sync_mut/security/remote_quorum.spl`: replicated session adapter quorum behavior.
- `src/lib/nogc_sync_mut/security/kms_provider.spl`: generic JSON-over-HTTPS KMS/HSM signing provider contract.
- `src/lib/nogc_sync_mut/security/kms_vendor_adapters.spl`: AWS, GCP, Azure, and PKCS#11 gateway request builders.
- `src/lib/nogc_sync_mut/security/enforcement/capability.spl`: runtime capability-handle checks.
- `src/lib/nogc_sync_mut/security/enforcement/gate.spl` and `src/lib/nogc_sync_mut/security/enforcement/resolver.spl`: gate and policy resolution.
- `src/lib/nogc_sync_mut/http/path_security.spl` plus HTTP server dispatch tests: safe request metadata reconstruction and handler scoping.

Backend security owns lowering installation points:

- `src/compiler_rust/compiler/src/interpreter_extern/sandbox.rs`: interpreter and Simple VM sandbox/control-plane externs.
- `src/compiler_rust/compiler/src/interpreter_extern/network/http.rs`: HTTP transport request handling bridge.
- `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs`: native runtime registration bridge.
- `src/compiler_rust/compiler/src/pipeline/native_project/*`: hosted native metadata embedding and native project checks.
- `src/compiler_rust/compiler/src/hir/capability.rs`: compiler-side capability item representation.

Live provider validation is intentionally outside hermetic CI:

- `.github/workflows/live-kms-security.yml`: manual-only live KMS workflow.
- `scripts/check/check-live-kms-security-workflow.shs`: local structural workflow checker.
- `scripts/check/check-repo-hygiene.shs`: repo hygiene integration.
- `doc/07_guide/security/live_kms_security_gates.md`: operator guide.
- `test/system/code_quality/live_kms_security_workflow_spec.spl`: Simple canary for workflow and guide invariants.

## Tree-Level Encapsulation

Tree-private is the default.

- Feature layers may call the next declared layer for the same feature without a gate.
- Same-feature calls that skip one or more intermediate layers emit `SEC101`.
- Cross-feature calls require a security gate and otherwise emit `SEC201`.
- `src/security/gate` may expose only gate facades. Gate implementation details stay private to the security tree.
- Source policy rules are authoritative unless marked `configurable`; `final` and non-configurable source rules cannot be weakened by SDN config.
- UI policy entries are display-only observations. They never grant server authority.
- Runtime `SecurityContext` authority is scoped by scheduler task id. Thread-local state is only a cache; async functions using `thread_local SecurityContext` emit `SEC501`.
- Remote requests are anonymous unless opt-in validation succeeds. Validated tokens reconstruct server-side context only after session-token agreement, expiry checks, and signature validation.

## Common Relative Tree Nodes

These common nodes are shared contracts, not layer-private implementations:

| Common node | Owner path | Purpose |
| --- | --- | --- |
| `security_coordinate` | `src/compiler_rust/compiler/src/security.rs` | Inferred `layer`, `feature`, `trust`, `runtime`, and security root facts. |
| `security_graph_edge` | `src/compiler_rust/compiler/src/security.rs` | Source and HIR feature/layer access edges. |
| `security_inventory` | `src/compiler_rust/compiler/src/security.rs` | Generated artifact source for maps, access matrix, UI policy, report, and sandbox lowering. |
| `runtime_security_context` | `src/lib/nogc_sync_mut/security/types.spl` | Runtime identity and authority container. |
| `remote_security_token` | `src/lib/nogc_sync_mut/security/types.spl` | Signed remote context token and key-id validation metadata. |
| `remote_session_store` | `src/lib/nogc_sync_mut/security/remote_redis.spl`, `src/lib/nogc_sync_mut/security/remote_quorum.spl` | Session lookup, refresh, revocation, persistence, and quorum merge. |
| `sandbox_lowering` | `src/compiler_rust/compiler/src/security.rs` | Abstract sandbox policy lowered to backend-specific enforcement metadata. |
| `capability_handle` | `src/lib/nogc_sync_mut/security/enforcement/capability.spl`, `src/compiler_rust/compiler/src/hir/capability.rs` | Runtime and compiler representation of granted authority. |
| `kms_signing_provider` | `src/lib/nogc_sync_mut/security/kms_provider.spl` | Opaque key-handle signing and verification contract. |
| `kms_vendor_request` | `src/lib/nogc_sync_mut/security/kms_vendor_adapters.spl` | Provider-specific AWS, GCP, Azure, and PKCS#11 gateway transport shapes. |

## Public Surface To Next Layer

| From layer | Public to next layer | Private |
| --- | --- | --- |
| `ui` | Display-only `ui_policy.sdn` observations and calls to `api`. | Authorization decisions and server authority. |
| `api` | Request DTOs and safe metadata for `service`. | Raw remote bearer authority before validation. |
| `service` | Application operations and task-scoped context entry for `domain`. | Worker/fd identity fallback as authority. |
| `domain` | Domain ports and policy decisions for `port`. | Direct concrete infra access. |
| `port` | Abstract persistence, KMS, session, and capability interfaces for `infra`. | Provider secrets and backend-specific request signing. |
| `infra` | Concrete Redis, KMS/HSM, HTTP, and sandbox adapter calls for `driver`. | Cross-feature bypasses and ambient capabilities. |
| `driver` | Runtime/backend install operations for `kernel`. | Unmapped host imports and undeclared sandbox capabilities. |
| `kernel` | Syscall/capability enforcement results. | Capability mutation outside generated manifests or pledged task capability sets. |
| `security/gate` | Explicit cross-feature gate facades. | Gate internals and raw policy data. |
| `security/policy` | Final/configurable policy contracts and diagnostics. | Silent weakening by generated or SDN config. |
| `security/sandbox` | Abstract sandbox policies and `sandbox_lowering.sdn`. | Backend-specific enforcement hidden from inventory. |

## Visibility Matrix

Each populated cell states the public contract to the parent node and the public contract to the next-layer sibling.

| Raw layer | `security_coordinate` | `security_inventory` | `runtime_security_context` | `remote_session_store` | `sandbox_lowering` | `capability_handle` | `kms_signing_provider` |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `ui` | Parent: path-derived feature/layer. Next: API call may carry display hints only. | Parent: consumes `ui_policy.sdn`. Next: no authority grant. | Parent: observes current user snapshot. Next: no context minting. | | | | |
| `api` | Parent: request entry layer. Next: service receives safe metadata. | Parent: access matrix explains denied edges. Next: diagnostics, not bypasses. | Parent: reconstruct only after validation. Next: pass scoped context to service. | Parent: lookup by session token. Next: no raw store mutation. | | | |
| `service` | Parent: same-feature layer descent. Next: domain call must be adjacent. | Parent: report and audit rows. Next: remediation targets. | Parent: scheduler task id owns scope. Next: explicit context helper. | Parent: refresh and revoke sessions. Next: revocation-wins state. | Parent: selects abstract sandbox policy. Next: no backend install. | Parent: checks active grant. Next: no ambient capability. | Parent: asks signing provider. Next: opaque key handles only. |
| `domain` | Parent: policy feature coordinate. Next: port interfaces. | Parent: final/configurable policy facts. Next: no direct infra. | Parent: policy sees explicit context. Next: no thread-local semantic dependency. | Parent: session semantics. Next: adapter-independent rows. | Parent: abstract capability needs. Next: backend-independent metadata. | Parent: declared authority classes. Next: port abstractions. | Parent: signing intent. Next: provider-neutral request. |
| `port` | Parent: port feature coordinate. Next: infra adapters. | Parent: generated backend targets. Next: adapter contract. | Parent: context required for privileged port calls. Next: scoped adapter invocation. | Parent: session adapter interface. Next: Redis/quorum implementation. | Parent: Linux/WASI/VM/baremetal/SimpleOS target rows. Next: concrete install plan. | Parent: capability classes. Next: concrete handle mapping. | Parent: generic JSON-over-HTTPS contract. Next: vendor builder. |
| `infra` | Parent: concrete backend coordinate. Next: driver install. | Parent: backend observation state. Next: install evidence. | Parent: validated context reaches backend. Next: no unauthenticated authority. | Parent: Redis TTL and tombstone rows. Next: quorum merge. | Parent: Landlock/seccomp/WASI/VM/PMP/object-cap plans. Next: runtime install. | Parent: runtime registry metadata. Next: reject ungranted use. | Parent: AWS/GCP/Azure/HSM requests. Next: no raw signing key in handler. |
| `driver` | Parent: runtime driver coordinate. Next: kernel/syscall bridge. | Parent: install checks. Next: backend result rows. | Parent: task id bridge. Next: syscall context. | | Parent: Simple VM import table and hosted native registry. Next: kernel pledges. | Parent: active table. Next: syscall check inputs. | |
| `kernel` | Parent: kernel feature coordinate. Next: none. | Parent: enforcement evidence. Next: none. | Parent: task identity. Next: none. | | Parent: SimpleOS `CapabilitySet`, RISC-V PMP CSR write plan, baremetal static sections. Next: none. | Parent: deny ungranted syscall authority. Next: none. | |

## Backend Lowering Architecture

`sandbox_lowering.sdn` is the compile-time bridge from abstract sandbox policy to runtime/backend enforcement:

- Linux hosted backends lower to Landlock filesystem rules and seccomp-BPF syscall classes. Installation sets `no_new_privs` before restricting the current process.
- WASI lowering populates an explicit capability table. Attached tables deny undeclared environment variables and preopened directories.
- Simple VM lowering populates `simple_vm_capability_table`, denies unmapped host imports by default, and preserves explicit `rt_security_*` control-plane imports.
- Baremetal lowering emits deterministic MPU/linker metadata. Linker scripts keep generated static capability/MPU sections and kernel install fails closed when required sections are absent.
- RISC-V baremetal lowering converts PMP metadata into `pmpaddrN` and `pmpcfgN` CSR write plans, including NAPOT encoding and locked read/write/execute config bytes.
- SimpleOS native lowering installs generated object-capability handles as pledged per-task `CapabilitySet` records.
- Hosted native builds embed lowering metadata into the runtime security registry so installation checks can observe backend and capability-handle state.

## Remote Security Context Architecture

Remote `SecurityContext` reconstruction is opt-in:

1. HTTP dispatch extracts safe request metadata.
2. If validation is disabled or the token is absent, the request runs anonymous.
3. If validation is enabled, the dispatcher validates key id, signature, expiry, session-token agreement, and session state.
4. Accepted context is scoped through scheduler-owned task identity around handler execution.
5. Polling and handler scopes use the unified runtime task selector so worker/fd identity cannot become authority.

Lifecycle state supports:

- key-id signing key rotation, refresh, revocation, and explicit key retirement;
- SDN export/import for key rings and session stores;
- distributed merge with revocation-wins and latest-active-expiry semantics;
- Redis-backed deployment storage using Redis TTLs for active expiry and bounded tombstones for revoked sessions;
- quorum read/write behavior over replicated session adapters;
- hosted adapter seams for opaque key rollout providers and replicated session storage.

KMS/HSM signing uses opaque key handles:

- `kms_provider.spl` defines the generic JSON-over-HTTPS sign/verify contract.
- `kms_vendor_adapters.spl` builds AWS KMS, Google Cloud KMS, Azure Key Vault, and PKCS#11 HSM gateway transport requests.
- Request handlers do not need raw signing keys.
- AWS OIDC live mode uses temporary AWS credentials and SigV4, including `x-amz-security-token` in both headers and signed headers.

## Live KMS CI Hardening

The live KMS gate remains outside normal CI execution:

- `.github/workflows/live-kms-security.yml` is manual-only through `workflow_dispatch`.
- Provider jobs use protected environments: `live-kms-aws`, `live-kms-gcp`, `live-kms-azure`, and `live-kms-hsm`.
- Provider preflight checks fail before live execution when required credentials or OIDC bootstrap variables are missing.
- `SIMPLE_LIVE_KMS_PROVIDER` selects the same Simple integration spec for each provider lane.
- `scripts/check/check-live-kms-security-workflow.shs` guards workflow shape locally and optionally runs `actionlint` when present.
- `scripts/check/check-repo-hygiene.shs` includes the live workflow checker without requiring cloud credentials or network access.
- Top-level workflow permissions stay at `contents: read`; AWS/GCP/Azure OIDC jobs add job-scoped `id-token: write`.
- The `auth` selector preserves `secret` mode and adds `oidc` mode for provider-by-provider migration.

## Diagnostics And Artifacts

Compiler and CLI output must stay deterministic over the checked source set:

- `SEC101`: same-feature layer skip, including convention-first paths such as `ui -> domain`.
- `SEC201`: cross-feature access without a security gate.
- `SEC501`: async function using `thread_local SecurityContext`.
- `layer_map.sdn`: generated layer facts.
- `feature_map.sdn`: generated feature facts.
- `gate_map.sdn`: inferred and explicit gate boundaries.
- `access_matrix.sdn`: feature/layer access decisions.
- `ui_policy.sdn`: display-only permission snapshots with stable observation keys, conditions, and policy version.
- `sandbox_lowering.sdn`: backend-specific sandbox enforcement plans.
- `report.md`: human-readable security audit report.

## Requirement Traceability

| Requirement | Architecture coverage |
| --- | --- |
| `REQ-001`, `REQ-002`, `REQ-003`, `REQ-004`, `REQ-005`, `REQ-006` | Convention-first and legacy coordinate inference plus same-feature layer enforcement. |
| `REQ-007`, `REQ-008`, `REQ-009` | Generated layer, feature, and gate maps. |
| `REQ-010` | Async `SecurityContext` misuse diagnostic. |
| `REQ-011`, `REQ-012`, `REQ-013`, `REQ-014`, `REQ-015` | Generated audit artifacts, source policy metadata, UI policy declarations, and minimal `security:` grammar. |
| `REQ-016`, `REQ-017`, `REQ-018`, `REQ-019`, `REQ-020`, `REQ-021`, `REQ-022` | Task-scoped context propagation, HTTP reconstruction, remote token validation, runtime metadata, scheduler task identity, and lifecycle primitives. |
| `REQ-023`, `REQ-024`, `REQ-025`, `REQ-026`, `REQ-027`, `REQ-028`, `REQ-029`, `REQ-030`, `REQ-031` | Hosted, future fiber, SimpleOS, distributed lifecycle, Simple VM, Linux, WASI, baremetal, and RISC-V sandbox enforcement. |
| `REQ-032`, `REQ-033`, `REQ-034`, `REQ-035`, `REQ-036`, `REQ-037` | Replicated session adapters, RISC-V PMP write plans, Redis deployment store, quorum behavior, KMS/HSM provider contract, and vendor request builders. |
| `REQ-LKMS-CI-001`, `REQ-LKMS-CI-002`, `REQ-LKMS-CI-003`, `REQ-LKMS-CI-004` | Manual live KMS workflow, protected environments, hygiene checker, and operator guide. |
| `REQ-LKMS-CI-005`, `REQ-LKMS-CI-006`, `REQ-LKMS-CI-007`, `REQ-LKMS-CI-008` | Secret/OIDC auth selector, GCP/Azure bearer minting, and AWS SigV4 OIDC execution. |
| `NFR-001`, `NFR-002`, `NFR-003`, `NFR-004` | Deterministic inference without extra full-tree scans, stable diagnostics, existing diagnostic preservation, and focused compiler tests. |
| `NFR-LKMS-CI-001`, `NFR-LKMS-CI-002`, `NFR-LKMS-CI-003`, `NFR-LKMS-CI-004`, `NFR-LKMS-CI-005`, `NFR-LKMS-CI-006` | Credential-free local checker, optional `actionlint`, minimum permissions, hermetic/live separation, job-scoped OIDC permission, and preserved secret mode. |

## Migration Sequence

1. Keep both coordinate layouts live until downstream projects finish moving from `src/feature/<feature>/<layer>` to `src/<layer>/<feature...>`.
2. Generate maps and reports from the compiler inventory before tightening runtime enforcement.
3. Route HTTP handler context through scheduler task ids everywhere, then retire worker/fd fallback authority.
4. Install backend sandbox lowering in hosted, WASI, Simple VM, baremetal, RISC-V, and SimpleOS paths with fail-closed defaults.
5. Move live provider validation from secret credentials to OIDC lane by lane, preserving the `secret` compatibility path until provider environments are migrated.
