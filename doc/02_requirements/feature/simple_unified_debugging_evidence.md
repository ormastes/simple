<!-- codex-design -->
# Simple Unified Debugging and Evidence — Feature Requirements

**Status:** Approved for design
**Decision basis:** `doc/01_research/app/tools/simple_unified_debugging_evidence_2026-08-14.md`, especially §17
**Date:** 2026-08-14

## Scope

These requirements establish the shared contracts and first vertical slices. Later
runtime, desktop, mobile, server, and hardware adapters implement the same
contracts; they do not introduce another debugger service.

## Requirements

- **REQ-001 — Single session owner.** `DebugServiceV1` shall exclusively own
  mutable debug sessions. CLI, IDE-DAP, SPipe-MCP, and Lab clients shall use an
  opaque `DebugSessionId`, never retain mutable adapter values.
- **REQ-002 — Stable wire boundary.** Out-of-process adapters shall communicate
  through versioned `DebugWireV1`; protocol negotiation shall reject unsupported
  major versions with a structured error.
- **REQ-003 — Migration, not duplication.** Existing `DebugTarget`,
  `ProfileTarget`, and legacy `DebugBackend` shall be exposed through migration
  adapters with one documented retirement gate. DAP remains IDE-facing.
- **REQ-004 — Small operation surface.** The root service shall expose Observe,
  Inspect, Control, Probe, Profile, Evidence, and registered versioned Domain
  operations. Domain-specific commands shall not expand the root protocol.
- **REQ-005 — Truthful target graph.** `DebugTargetGraphV1` shall describe typed
  parent/child and boundary edges for host, runtime, task/actor, browser, DB,
  device, UI/GPU, and embedded targets without fabricating unavailable nodes.
- **REQ-006 — Capability honesty.** `DebugCapabilityV1` shall report support
  (`Native | Emulated | Unavailable`), verification (`LiveVerified |
  FixtureVerified | Unverified | Blocked`), and perturbation (`Passive |
  Cooperative | Stopping | Mutating`) independently.
- **REQ-007 — Correlated events.** `DebugEventV1` shall carry an exact build ID,
  source/symbol anchors when available, domain correlation IDs, clocks, privacy
  labels, typed payload, and `Observed | Caused` provenance.
- **REQ-008 — Native plus normalized evidence.** Evidence export shall retain raw
  native artifacts and create a normalized, manifest-indexed bundle. Successful
  parsing shall not be represented as resolution of the originating defect.
- **REQ-009 — Receipted actions.** Every attach, probe, control, mutation,
  capture, replay, and cleanup action shall emit `DebugReceiptV1` recording
  actor/session, exact build, policy decision, time, perturbation, outcome, and
  whether execution changed.
- **REQ-010 — Enforced policy.** `DebugPolicyV1` shall authorize Observe and
  Control separately, enforce privacy/redaction, TTL, rate, retention,
  environment and privilege constraints, and deny unapproved mutations.
- **REQ-011 — Unified probes.** Stop, Log, Trace, Watch, Count, Snapshot, and Dump
  probes shall share one lifecycle and map to adapter-native mechanisms.
  Temporary probes shall be enumerable and removable.
- **REQ-012 — Read-only AOP default.** Debug aspects shall contain no business
  logic, use typed fields and stable callsite IDs, support sampling/rate limits
  and TTL, and be rejected in mission-critical validation if they can mutate
  semantics.
- **REQ-013 — Live doctor.** `simple debug doctor [profile.sdn]` shall test actual
  adapter reachability and report each capability, verification tier,
  perturbation, privilege, tool version, and blocked reason. Source presence
  alone shall never yield a verified result.
- **REQ-014 — Minimal CLI.** The service shall support `simple debug`, `doctor`,
  `inspect`, `probe apply|remove|list`, `reproduce`, and `replay`, with rich
  configuration represented in SDN profiles rather than flag proliferation.
- **REQ-015 — First vertical slices.** Delivery shall prove the shared contract
  with Simple interpreter, SQLite, Chrome JS/Wasm/Simple-script, and embedded
  custom-dump plus OpenOCD/T32 slices, in that order unless a recorded dependency
  requires otherwise.
- **REQ-016 — Cross-language stacks.** Browser adapters shall use
  `BoundaryFrameV1` and exact source-map/DWARF provenance to construct logical
  JS/Wasm/Simple stacks; source-breakpoint claims require a real breakpoint test.
- **REQ-017 — SQL causality.** `QueryDebugV1` shall correlate sanitized SQL,
  source, task/actor/trace and transaction identity with plans, execution stats,
  waits/locks, errors and raw engine evidence. Bind values shall be excluded by
  default.
- **REQ-018 — Embedded evidence first.** Embedded workflows shall prefer retained
  dump/trace and passive event rings before halt/control, reuse JTAG/DMI/OBS,
  GDB remote, OpenOCD and T32 support, and bind source breakpoints by `SymbolId +
  SourceAnchor`.
- **REQ-019 — Evidence-driven investigation.** SPipe debugging guidance shall
  implement D0–D12 intake, preservation, doctor, classification, budgets,
  observation, reproduction, hypothesis, attach, ownership, test decision,
  fix/verify, cleanup, and knowledge-update stages.
- **REQ-020 — Knowledge and cost learning.** On debug completion, the workflow
  shall decide whether reusable knowledge was learned. Each resolved bug shall
  record provider-reported token usage (or explicit unavailable), comparable
  bug-fix average, and ratio; a ratio greater than 2.0 shall require a linked
  knowledge/skill/tool update before closure.

## Exclusions for the contract wave

Arbitrary production evaluation, unrestricted memory writes, universal replay,
and simultaneous completion of every language/runtime adapter are excluded.
They require explicit policy and domain acceptance evidence in later waves.
