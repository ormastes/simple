# Caret CoreMux A/N2 implementation lanes

2026-10-25. Root accepted the corrected interface shape and discovery slice as
the next stage; a bounded discovery contract source slice is being implemented,
not a working full provider. User selected A and N2, but
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
| D6I IDE integration | Actual IDE/editor extension composition and Caret terminal entry; preserve shared semantic UI | D3+D4+D6; wire real child/terminal owner before tests. Existing terminal line model/profile activation is not implementation evidence. Root assigns source paths before edits |
| D6A all shared-API applications | Web and LLM dashboard REST/WS routes, configured std.tmux families, hosted/OS-shell consumers and runtime-discovered plugins | D3+D4+D5; audit A01–A10, repair owner error/quoting semantics before mounting dormant routes, preserve explicit selection, no silently excluded caller |
| D7 optional capabilities/UI | terminal extension implementations and existing Caret UI composition | Required CoreMux workflows complete first; only extra features optional; no new renderer |
| V1 native/spec/manual qualification | system-test lane's plan, actual Caret/IDE/all-application SYSTEM SSpecs, captures/manuals and SDN receipts | D6+D6I+D6A and genuine Phase3 admission/full CLI; real application process/terminal/layout/messaging/cleanup effects, legacy formats and optional refusal independently |
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
REQ-CMUX-001..012 and NFR-CMUX-001..009 to actual assertions/evidence. Retain
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

## Mandatory application closure and actual execution ownership

Latest explicit user scope includes the complete Caret suite, IDE integration
and **every application using shared pane/mux APIs**. This is mandatory
REQ-CMUX-012, not a newly proposed optional feature. The source inventory is
`doc/09_report/shared_mux_application_inventory_2026-10-25.md`; the system plan
contains the A01–A10 application-to-test matrix. Runtime plugin/dynamic-selector
consumers discovered later must join that manifest before qualification.

| Owner lane | Required application rows | Reviewable completion evidence |
| --- | --- | --- |
| Caret source owner | A01 dashboard, A02 workspace, A03 workbench GUI/TUI, A10 swarm | Real entrypoints on selected owners, no synthetic PID/pane success; actual command/output and native message delivery, owned child lifecycle |
| IDE/extension source owner (root assignment required) | A09 IDE/editor/plugin host | Production extension/command reaches real CoreMux; actual IDE process and terminal effects, focus/layout/resize, messages and reopen/cleanup. A line-array renderer cannot close this lane |
| Shared applications source owner (root assignment required) | A06 web dashboard, A07 LLM dashboard, A08 configured library consumers | Mounted real routes, preserved HTTP/WS protocol, backend failure propagation and safe targets, observable child state, no hardcoded empty success or fallback |
| SMUX/host composition owners | A04 hosted product, A05 shell/OS registrations | Verified Phase 3-built product; actual owner/client/loader and terminal execution. Guest claims require real guest evidence |
| System-test owner | Shared contract and complete A01–A10 traceability | Modern `step(...)` SYSTEM scenarios against actual apps/fixtures; helpers `caret_mux_setup`, `caret_mux_check_state`; no new test wrappers or fake backend |
| Root execution/merge owner | Producer admission, resource schedule, attempts and final integration | Existing Phase2 checks without a Phase2 rebuild, then actual Phase3 compiler/runtime/Hello lineage for Phase3 qualification; actual native runs, case counts, artifacts, six-cycle ledger, material repair then affected rerun |

Prerequisite failures remain explicit: missing real backend, Phase 3 CLI,
runtime/provider, application route or native fixture means BLOCKED/NOT_RUN.
Do not create empty/fake-fail placeholder tests to imply a delivered system
suite. Once the production route is runnable, the actual scenario must fail
when its fixture is missing; no opt-in skip can count as a passed feature.

Execution results retain discovered, executed, passed, failed, blocked and
not-run case counts with binary/source/backend/runtime/host identities. Keep
original failure output, process-tree terminal receipts, captured native state
and cleanup artifacts before repair. Fix the owning implementation and rerun
affected cases only, counting all prior attempts across sessions/worktrees
toward six. No authored scenario, parsed command, test listing, model snapshot
or adapter-only result is a replacement for the user's required real SYSTEM
execution. Existing messaging and independent owner/client suites are reused
at their actual boundaries, not duplicated or promoted beyond their evidence.

N2 remains additive: all application correctness rows plus both backend latency,
stress, stale-reference/crash checks and genuine 24-hour soaks are required.
Source work may proceed within root-approved ownership while native gates are
blocked, but no lane is reported qualified or finished solely from source.
