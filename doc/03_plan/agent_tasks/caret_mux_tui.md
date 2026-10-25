# Caret CoreMux A/N2 implementation lanes

2026-10-25. Root accepted the corrected interface shape and discovery slice as
the next stage; production implementation is not started. User selected A and N2, but
neither selection nor these artifacts establish a working provider. No Phase2
rebuild/seed fallback. Preserve existing concurrent smux changes and unrelated
golden image modifications; merge owner/root integrates only reviewed scope.

## Shared names and ownership

Architecture: ../../04_architecture/caret_mux_tui.md.
Detail contract: ../../05_design/caret_mux_tui.md.
Requirements: ../../02_requirements/feature/caret_mux_tui.md and NFR counterpart.
Names: CoreMuxV1, MuxHandleV1, MuxObjectRefV1, MuxErrorV1, MuxSnapshotV1,
MuxQueryV1/MuxQueryResultV1, MuxCommandV1/MuxRequestV1/MuxMutationV1,
MuxCapabilityV1, MuxTerminalLeaseV1, TerminalLayoutV1, TerminalPresentationV1.
Core facade mux_connect_v1/query_v1/execute_v1/poll_events_v1/disconnect_v1;
optional mux_acquire_terminal_layout_v1/mux_acquire_terminal_presentation_v1.
All short names above carry the mux_ prefix as spelled in detail design.

The root is merge owner and interface approval owner. Best available Astra/root
performs final cross-lane semantic/ownership review and generated-manual review.
Lower-model implementation sidecars: N/A at this stage; existing Astra source
audit and independent reviews supply evidence. Do not start new sidecars before
the shared interfaces and owned paths are accepted.

## Ordered graph

| Lane | Deliverable/paths | Dependencies and stop criterion |
|---|---|---|
| D0 contract review | Root reviews the three design files, selected requirements and exact caller matrix | Resolve interfaces, namespace authority, capability/commit semantics; no implementation before approval |
| D1 common contract | common/contracts/mux/core_v1.spl and terminal_v1.spl; focused pure validation controls | D0; no host calls or copied mutable sessions; exhaustive operation/error descriptors |
| D2 existing owner correctness | Current geometry/rollback, target/session and notification owners | Keep active agents' file scopes; actual owner semantics for all mandatory operations, no fake flag zoom |
| D3 smux provider and facade | os/apps/smux/core_mux_adapter.spl, nogc_sync_mut/sosix/mux composition | D1+D2; persistent namespace connect, lease/generation checks, typed query/execute, bounded queues |
| D4 real tmux provider | Sosix mux/tmux_control.spl, framed protocol/parser controls | D1; genuine tmux process, correlated response/notification streams; unsupported atomic plan explicit |
| D5 legacy connected adapter | hosted_apps/smux_tmux_compat.spl plus hosted smux entry composition | D3; full audited flags/target/format matrix connected to owner; preserve existing flags/output |
| D6 Caret migration | pane_backend, agent_workspace, standard wrappers and modeled swarm executor composition | D3+D4+D5; preserve existing signatures/semantics and real identities; no caller downgrade; one coordinated caller owner |
| D7 optional capabilities/UI | terminal extension implementations and existing Caret UI composition | Required CoreMux workflows complete first; only extra features optional; no new renderer |
| V1 native/spec/manual qualification | system-test lane's plan, real specs, captures/manuals and SDN receipts | Genuine Phase3 admission and full CLI; positive/negative effects, legacy formats and optional refusal independently |
| V2 N2 performance/soak | Two real backends, selected topology, 24h each, bounded floods/disruption | V1 correctness gates; record latency/RSS/cleanup distributions and actual elapsed time |
| L reviewed landing | Root PR to release/1.0.0 with exact-head review | Required verification PASS, accepted manuals, no unresolved material findings; release tags separate |

D3 and D4 can proceed independently after D1. D5 cannot be an unconnected pure
parser deliverable; its done criterion requires execution through actual smux
ownership. D6 cannot replace tmux calls with in-memory commands. D2 can finish
already-authorized corrections while D0 review is pending, but not appropriate
another lane's files. Dependencies on unavailable Phase3 block runtime evidence,
not honest source design/implementation approved by the root.

## Accepted next connected implementation slice

Start with a real discovery route, not a complete CoreMux full of Unsupported
branches: explicit ExistingOnly connect/owner generation, session metadata and
exact `has-session -t` projection through the hosted entry to the persistent
smux owner. Preserve existing flags; exact owner resolution distinguishes absent
and ambiguous targets, and legacy stdout/status stays tmux-compatible. This
slice does not qualify CoreMux or claim namespace auto-start, launch, capture,
layout or complete target grammar. Those remain mandatory later slices.

Bounded implementation file manifest:

- New common/contracts/mux/core_v1.spl: discovery request/result/error/identity
  subset and common MuxProviderPortV1, only implemented operations.
- New nogc_sync_mut/sosix/mux/mod.spl and smux_transport.spl: composition-owned
  registration and authenticated endpoint transport through existing Sosix
  network owners; no import of os/apps.
- New os/apps/smux/core_mux_adapter.spl: owner identity/session discovery,
  using existing smux_list_sessions and target semantics; no duplicate state.
- New hosted_apps/smux_tmux_compat.spl plus coordinated smux_client.spl route:
  exact argv parsing and status projection for the supported connected slice.
- Coordinated existing server.spl dispatch hook: bounded versioned discovery
  envelope on the existing authenticated server, preserving old commands.
- Focused production-connected tests selected by the system-test owner after
  interfaces compile; stale generation, missing/ambiguous target, cross-owner
  refusal and existing CLI preservation are required negative oracles.

Root assigns source ownership before edits. Endpoint discovery
must be designed with the namespace owner: no fixed port, hardcoded token,
unsafe predictable credential, or extra CLI flag that changes Caret calls.
If an existing namespace cannot yet resolve safely, finish that owner prerequisite
before exposing the legacy route. Import/capsule admission and native behavior
remain pending Phase3. No production edits are authorized by this proposal alone.

### D1 exact paths and validation split

- src/lib/common/contracts/mux/core_v1.spl: discovery subset records/enums
  MuxBackendV1, MuxHandleV1, MuxObjectRefV1, MuxConnectV1, MuxErrorV1,
  MuxCapabilityV1, MuxSessionSummaryV1, MuxDiscoveryV1 and MuxProviderPortV1.
  Do not populate unimplemented full CoreMux variants with successful defaults.
- src/lib/common/contracts/mux/validation_v1.spl: pure checked constructors
  mux_validate_namespace_v1, mux_make_connect_v1, mux_make_object_ref_v1 and
  mux_validate_discovery_v1. Validate nonempty/bounded namespace and IDs, enum
  kinds, positive generations, unique session IDs, bounded arrays and explicit
  backend/endpoint policy. Return typed errors, never host lookup or mutation.
- test/01_unit/lib/common/contracts/mux/core_v1_spec.spl: genuine validation
  controls for valid boundaries, empty/oversize identifiers, duplicate sessions,
  invalid generations and backend/policy combinations. No backend availability
  or lifecycle success assertions before a real provider is bound.

These constructors validate representation only. Provider registration/connect
must independently validate live authority, ownership, endpoint credentials,
generation and lease. A well-shaped public record is never an authentication
token. Full CoreMux bindings and optional terminal_v1 stay out of this initial
code slice; add each operation only with its real implementation and tests.
The following connected paths then complete the discovery route, under separate
owner assignment: src/lib/nogc_sync_mut/sosix/mux/mod.spl and smux_transport.spl;
src/os/apps/smux/core_mux_adapter.spl; src/app/hosted_apps/smux_tmux_compat.spl;
the existing src/app/hosted_apps/smux_client.spl and src/os/apps/smux/server.spl.
No facade may expose a model-only discovery result while that route is missing.

## Test design handoff and caps

The system-test owner writes doc/03_plan/sys_test/caret_mux_tui.md and the TUI
capture plan, then production-connected modern SSpec once interface code exists.
Shared helpers and manual step labels are fixed in the detail design; no success
placeholder or model-only availability test counts as execution. Map every
REQ-CMUX-001..011 and NFR-CMUX-001..009 to actual assertions/evidence. Retain
separate semantic, legacy CLI, optional-capability and provider-native rows.

N2 baseline is two namespaces, two sessions each, four panes/two clients per
namespace as the selected NFR states; report any stronger topology explicitly.
Each backend requires actual 24h elapsed soak. Fake time or reduced topology is
diagnostic evidence only. Missing backend/engine/producer is BLOCKED/NOT_RUN.
No more than six verify/fix cycles per feature across all worktrees/sessions;
root owns the attempt ledger. Never rerun unchanged green checks to manufacture
confidence. Reuse immutable evidence when source/provider/criterion is unchanged.

All new manifests/diagnostic records use SDN; retain required tmux text protocol
and historical evidence unchanged. Host access stays in Sosix/platform owners.
Final review checks native generation/runtime/Hello lineage, negative oracle
sensitivity, actual assertion counts, captures/manual quality and cleanup, not
just compilation or source hashes. No current row is marked runtime PASS.
