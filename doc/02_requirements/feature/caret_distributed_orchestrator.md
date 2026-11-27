# Caret distributed orchestrator requirements

## Preservation and current checkpoint

The selected requirements below are preserved from the existing main-worktree
plan, original SHA-256
`505978b66557b47f36eb37b63ac690d5b0ef2a677d5dc8d5dfe26811924fa274`.
The original file was read-only. Its delivery inventory, pending-kind notes and
evidence paths describe the original planning state, not current admission or
verification. No historical probe claim below is promoted to current evidence.
The current source/test/manual inventory and gaps are authoritative in
`doc/03_plan/sys_test/orchestrator_verification_wait_20261107.md`.
Status is **AWAITING_VERIFICATION**; no selected requirement is declared complete
merely because a schema or authored spec exists. The shorthand ORCH-01/02/03 IDs
here are distinct from the older ORCH-001..016 research IDs.

User-selected baseline: **Simple Caret distributed execution**, revision 1,
2026-11-06, supplied in the implementation request. Target: `release/1.0.0`.
The supplied plan's requirements are selected; this document does not introduce
alternative requirements or claim that the full system exists.

## Delivery inventory

| Requirement | Selected behavior | Current change |
| --- | --- | --- |
| CFG-01 | One strict SDN dispatch path for configuration, workloads, and combined resources | Unverified source: Pod/Deployment/Job/Pipeline, ResourceProfile and ResourceList; other configuration kinds pending |
| CFG-02 | Strict versioning, quantities, source locations, identities, references and immutable plans | Partial: versions, nested errors, duplicate identities and checked quantities |
| DAE-01 | Safe response commit | Unverified source: legacy failure blocking and V2 retained-outcome publication; complete crash-safe service composition pending |
| DAE-03 | Reused operation journal | Shared SDK admission/begin/outcome mechanism extracted and consumed by BuildRunner; runtime verification pending |
| DAE-02/04/05 | Exact ownership, bounded async dispatch and durability | Pending |
| HOST-01..03 | Authenticated enrollment, strict physical-scope admission and recovery | Provisional native capacity/codec probes pass; shared-journal preparation adapter authored but native build blocked in PureSQL; full host composition/recovery pending |
| ORCH-01 | Placement and profiles | Unverified profile decode and CPU/memory proposals; host placement pending |
| ORCH-02..03 | Fenced assignment, fairness and scarce-resource policy | Pending |
| CTR-01..03 | Podman streams, exact cleanup and Windows Docker process provider | Pending; existing OCI/CI code remains the reuse target |
| MUX-01..02 | Typed owner composition and distinct control authority | Pending |
| CARET-01..02 | IaC-backed creation and explicit CLI adapters | Pending |
| RUN-01..02 | Shared execution adapter and parent-verified remote evidence | Pending |
| OPS-01 | Correlated inspect/explain/logs/audit | Pending |
| EXT-01 | Separately qualified FreeBSD, Apple and Kubernetes backends | Pending |

## First change acceptance

- REQ-CFG-01-A: Decode a singleton or a ResourceList using one canonical parser
  invocation. Dispatch child values without serialization or reparsing.
- REQ-CFG-01-B: Preserve Pod/Deployment/Job/Pipeline source entrypoints, typed
  values and valid behavior. Flatten nested lists in declaration order.
- REQ-CFG-02-A: Reject duplicate/unknown keys, unsupported version/kind pairs,
  wrong types and malformed children for the entire set, with original spans.
- REQ-CFG-02-B: Reject duplicate group/kind/namespace/name across the entire
  flattened set. List metadata never changes a child's namespace.
- REQ-CFG-02-C: Reject resource quantity overflow before arithmetic; preserve
  exact valid signed 64-bit quantities.
- REQ-CFG-02-D: Bound source length, pending resource nodes and list depth.

Empty lists are accepted as no-op decoded sets. A decoded set is **not** an
authorized/resolved plan. HostPool, RuntimeClass, AgentSession,
HostConfig, reference resolution, digest binding and apply remain pending and
must not be advertised by a controller yet. AT-CFG-01 now has authored
configuration-only, workload-only and combined scenarios; runtime evidence is
still NOT_RUN.

## Profile and proposal acceptance

- REQ-ORCH-01-A: Decode cpu/memory min/recommend/prefer/limit, enforcing
  nonnegative ordered values and the selected progressive defaults.
- REQ-ORCH-01-B: A normal CPU/memory proposal targets the recommendation;
  explicitly allowed opportunistic proposals target the preference. Capacity
  below either minimum rejects; between minimum and target is reported as
  constrained where below recommendation.
- REQ-ORCH-01-C: Effective cap equals selected allocation. A larger declared
  limit does not become a larger reservation or effective cap.
- REQ-ORCH-01-D: Preserve GPU requirement and scarce-host preference. A CPU/memory
  proposal retains an explicit unresolved-GPU flag; it is never a device grant.
- REQ-ORCH-01-E: Revalidate ranges for programmatically constructed profiles.

The initial GPU schema accepts only `required`; unknown sharing or device fields
reject. A required GPU profile may be stored as configuration but cannot become
a host assignment until the explicit device-claim path is implemented.

Evidence: `test/03_system/app/orchestrator/feature/resource_set_spec.spl` plus
`resource_profile_spec.spl` in the same directory and existing orchestration unit
specs. Authored scenarios are NOT_RUN, not PASS.
