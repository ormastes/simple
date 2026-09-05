<!-- codex-design -->
# Simple Unified Debugging and Evidence Architecture

**Status:** Approved design baseline
**Date:** 2026-08-14

## Decision

Use one centrally owned, versioned `DebugServiceV1`. Clients hold
`DebugSessionId`; they never own mutable adapters. DAP is an outward protocol,
not a second service. Existing `DebugTarget`, `ProfileTarget`, and legacy
`DebugBackend` enter through adapters. Out-of-process domains speak
`DebugWireV1`.

```text
CLI     IDE-DAP     SPipe-MCP     Lab
  \        |           |          /
       client façades / policy context
                    |
             DebugServiceV1
       session registry + operation router
          /          |            \
 Target Graph   Evidence Store   Policy/Receipts
          \          |            /
       isolated DebugWireV1 adapter hosts
 Simple | Native | Browser | SQL | Embedded | later domains
```

## Contract capsule

The contract owner publishes only:

- `DebugSessionId`, lifecycle and bounded session registry;
- `DebugServiceV1` operations: Observe, Inspect, Control, Probe, Profile,
  Evidence, and registered Domain commands;
- `DebugWireV1` envelope, negotiation, deadline, cancellation, streaming and
  structured error rules;
- `DebugTargetGraphV1`, `DebugCapabilityV1`, `DebugEventV1`, `DebugReceiptV1`,
  and `DebugPolicyV1`;
- typed extension registration, never arbitrary maps at the root boundary.

This is an MDSOC virtual capsule: domain implementations remain sibling-private
and are visible upward only through the contract. Cross-cutting receipt,
redaction, build-binding and correlation behavior is applied at the service
boundary as a feature transform, not copied into adapters.

## Ownership and value semantics

The session registry owns each mutable adapter exactly once and serializes or
owner-routes mutations per session. Clients receive immutable snapshots and
IDs. This avoids the documented Simple value-semantics hazards in capability
handles: no paired mutable trait copies, no mutation through `fn`, and no
aliasing assumption. Adapter calls return owner results that the registry
commits deterministically.

## Request path

1. Authenticate client and resolve `DebugSessionId` in O(1) indexed lookup.
2. Classify the operation and evaluate `DebugPolicyV1` before adapter dispatch.
3. Allocate a receipt ID and record attempted action.
4. Dispatch to the owning in-process adapter or bounded `DebugWireV1` host.
5. Validate build identity, payload limits and adapter response.
6. Commit graph/event/evidence changes and finalize `DebugReceiptV1`.
7. Return an immutable result. A disconnect does not cancel required cleanup.

Observe does not silently escalate to Control. Any operation that can stop or
change execution is classified before dispatch.

## Target graph and causality

Nodes have stable session-local IDs, kind, lifecycle, build identity and
capabilities. Typed edges express ownership, containment, execution boundary,
message/RPC, source/generated-code, render, storage and device relations.
Events use monotonic and domain clocks plus optional wall time; clock mappings
are evidence, not assumptions. `BoundaryFrameV1` supplies logical stack edges.

## Evidence architecture

Raw bytes are append-only content-addressed artifacts. Normalizers produce SDN
indexes referencing raw digests; they never replace native evidence. A bundle
contains manifest, receipts, normalized targets/events/stacks/query plans, raw
artifacts, media and an evidence showcase. Offline inspection requires no live
adapter. Parser success and root-cause resolution are separate states.

## Adapter lifecycle and failure isolation

Default external adapters run out of process with protocol/version negotiation,
bounded frames, heartbeats, deadlines, cancellation and crash supervision.
Restart never reuses a stale mutable session. An adapter declares domains and
capabilities only after a live or fixture verification transaction. Cache keys
include adapter version, target identity, build ID and policy/redaction version;
disconnect, build change, target lifecycle, policy change and explicit refresh
invalidate affected entries.

## Startup and hot-path design

Startup loads the contract registry, policy and adapter manifests only; it does
not discover every target or scan the repository. Adapter discovery is lazy and
cached. Session lookup and command routing do not shell out. Doctor may invoke
external tools concurrently under declared deadlines and reports their wait
separately. Event ingestion uses bounded rings/batches and backpressure with
drop counters. Timings, queue depth, drops, adapter restarts, policy denials,
cache hits/misses and evidence bytes are observable.

## Compatibility and migration

One adapter maps current `DebugTarget`/`ProfileTarget`; one maps legacy
`DebugBackend`. Their retirement gate requires all consumers migrated, parity
tests green, no direct construction outside the owner, and a deprecation cycle.
DAP handlers translate to service operations and preserve DAP behavior.

### Existing-tool harmony lock

`DebugServiceV1` is a lifecycle/policy/evidence owner, not a fifth debugger.
The following landed mechanisms remain authoritative behind adapters:

- DAP: `app/dap/target_session.spl` and the outward stdio server;
- MCP: `app/mcp/dap_bridge.spl` and its existing tool names;
- GDB/LLDB: the long-lived mcpgdb process/FIFO runners;
- embedded selection: the canonical remote `session_model.spl` backend catalog
  and bootstrap plans, not the copied MCP catalog;
- TRACE32: existing native/GDB protocol clients, T32 session registry,
  PRACTICE/actions, window capture and snapshot store;
- OpenOCD/GDB-RSP/JTAG: existing protocol clients, TAP/DTM/DMI/link-mux and
  target-exec adapters;
- Windows: existing `DbgEngClient`/`DbgEngAdapter`, including native dump
  loading. ETW remains unavailable until a real adapter lands.

Their local process/device handles are backend resources keyed by one public
`DebugSessionId`. Existing registries may retain private resource lookup during
migration, but cannot remain independent public lifecycle owners. Existing
front-door protocols and command names remain stable. Capability feature bits
are translated into per-target `DebugCapabilityV1` rows; they do not imply
`LiveVerified`. Native dump/window/trace artifacts are indexed and retained,
not converted into replacement formats.

## Alternatives rejected

- Separate debugger services per domain: rejects shared identity, policy and
  evidence correlation.
- Put every command in the root API: makes versioning and isolation brittle.
- Let clients own adapters: violates central ownership and Simple value safety.
- Normalize and discard native dumps: destroys future forensic evidence.
- Treat source presence as capability support: produces dishonest doctor output.

## Delivery boundaries

Wave 0 freezes contracts. Wave 1 adds provenance/evidence. Wave 2 adds registry,
host, doctor, clients and migration. Wave 3 completes Simple-native debug. Wave
4 proves interpreter, SQLite, browser and embedded slices. Later waves add
cross-domain replay and the full live evidence matrix.

The first Wave 4 SQL slice is now executable for the repository's canonical
SQLite-compatible `PureDatabase`: Unit, Integration, and System scenarios bind
sanitized query identity, typed bind shape, source/trace/transaction context,
plan, timing, and row count to `QueryDebugV1`. C SQLite diagnostics and the
remaining browser/interpreter/embedded live matrices are not implied by that
slice and remain separate gates.
