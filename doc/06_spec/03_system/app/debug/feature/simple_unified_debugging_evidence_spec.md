# Unified debugging and evidence — Wave 0/2 contract

> This executable contract freezes the additive V1 boundary before domain adapters expand. It checks public names, the deliberately small operation surface, central mutable-session ownership, build-bound receipts, and explicit policy authorization.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unified debugging and evidence — Wave 0/2 contract

This executable contract freezes the additive V1 boundary before domain adapters expand. It checks public names, the deliberately small operation surface, central mutable-session ownership, build-bound receipts, and explicit policy authorization.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | [Unified debugging requirements](doc/02_requirements/feature/simple_unified_debugging_evidence.md) |
| Plan | [System-test plan](doc/03_plan/sys_test/simple_unified_debugging_evidence.md) |
| Design | [Unified detail design](doc/05_design/simple_unified_debugging_evidence.md) |
| Research | [Unified debugging research](doc/01_research/app/tools/simple_unified_debugging_evidence_2026-08-14.md) |
| Source | `test/03_system/app/debug/feature/simple_unified_debugging_evidence_spec.spl` |
| Updated | 2026-08-14 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This executable contract freezes the additive V1 boundary before domain
adapters expand. It checks public names, the deliberately small operation
surface, central mutable-session ownership, build-bound receipts, and explicit
policy authorization.

The contract is intentionally about shared service behavior. Existing DAP,
MCP, GDB/LLDB, TRACE32, OpenOCD, JTAG, and DbgEng mechanisms remain adapters.
Passing this specification never proves that one of those external tools is
installed, reachable, privileged, or live-verified.

**Requirements:** [Unified debugging requirements](doc/02_requirements/feature/simple_unified_debugging_evidence.md)

**NFR requirements:** [Unified debugging NFRs](doc/02_requirements/nfr/simple_unified_debugging_evidence.md)

**Research:** [Unified debugging research](doc/01_research/app/tools/simple_unified_debugging_evidence_2026-08-14.md)

**Plan:** [System-test plan](doc/03_plan/sys_test/simple_unified_debugging_evidence.md)

**Architecture:** [Unified architecture](doc/04_architecture/simple_unified_debugging_evidence.md)

**Design:** [Unified detail design](doc/05_design/simple_unified_debugging_evidence.md)

## Scope

The scenarios cover REQ-001 through REQ-007 and REQ-009 through REQ-010.
They cover the Wave 0 contract and selected Wave 2 ownership behavior.
They do not claim REQ-008 bundle materialization.
They do not claim the AOP validator in REQ-012.
They do not claim live doctor behavior in REQ-013.
They do not claim full CLI execution in REQ-014.
They do not claim domain slices in REQ-015 through REQ-018.
Those requirements have separate focused evidence and remaining release gates.

## How to run

Run the executable scenario with the pure-Simple self-hosted binary:

```text
bin/simple test \
  test/03_system/app/debug/feature/simple_unified_debugging_evidence_spec.spl \
  --mode=interpreter --no-session-daemon
```

Generate this manual with:

```text
bin/simple spipe-docgen \
  test/03_system/app/debug/feature/simple_unified_debugging_evidence_spec.spl \
  --output doc/06_spec --no-index
```

If the launcher identifies itself as the Rust bootstrap seed, the result is
focused diagnostic evidence only. Bootstrap Stage 4 remains authoritative.

## Syntax and examples

Open a session through `DebugServiceV1` and retain only `DebugSessionId`.
Associate every target capability with its exact `target_id`.
Build topology only from target IDs already present in the same session.
Authorize an operation before invoking its adapter mechanism.
Record support, verification, and perturbation independently.
Bind every receipt to the session build identity.
Close service state idempotently without claiming target execution changed.

## Scenario catalog

1. Every locked V1 public contract name has one definition.
2. Exact V1 wire peers negotiate successfully.
3. Additive V1 minor versions negotiate successfully.
4. Unsupported major versions fail structurally.
5. Malformed version strings fail structurally.
6. Capability support does not imply verification.
7. Capability verification does not imply perturbation.
8. The root operation set stays deliberately small.
9. Domain extension remains versioned and registered.
10. One service owns mutable session state.
11. Anonymous build identity is rejected.
12. Clients receive opaque, unique session IDs.
13. Policy authorization precedes action.
14. Receipts retain build and perturbation facts.
15. Mutation remains denied by the development default.
16. Target nodes and typed edges retain topology.
17. Missing topology endpoints fail closed.
18. Event contracts retain causality and privacy fields.
19. V1 remains additive to legacy traits.
20. Session receipt streams remain isolated.
21. Session close is idempotent.
22. Post-close operations are denied without execution change.

## Expected evidence

A passing run reports fourteen executed examples and zero failures.
The service runtime scenarios use real mutable `DebugServiceV1` values.
The wire scenarios execute real negotiation logic.
The topology scenario creates two nodes and one typed edge.
The policy scenarios inspect actual returned receipts.
The source-contract scenarios are interface-lock checks, not live adapters.

## Failure interpretation

A missing contract name means the interface lock changed.
A negotiation failure means wire compatibility changed.
A capability-dimension failure means truth states were collapsed.
A session collision means central ownership is broken.
A missing denial receipt means policy auditing is incomplete.
An accepted missing-endpoint edge means the graph can fabricate topology.
A post-close accepted action means stale session authority survived cleanup.

Do not repair a failure by weakening an assertion or adding a parallel API.
Inspect the owning contract/service and preserve existing adapter mechanisms.

## Explicit nonclaims

This specification does not attach to a real process.
It does not launch a DAP server.
It does not open an MCP transport.
It does not connect TRACE32 or OpenOCD.
It does not parse a Windows dump.
It does not export native evidence files.
It does not prove browser, SQL, mobile, or embedded domain behavior.
It does not prove performance, crash isolation, or bounded memory.

Those claims require live doctor rows, focused adapter tests, retained evidence,
and the pure-Simple Bootstrap-4 release gate.

## Scenarios

### REQ-002/004/006: locked versioned contracts

#### should expose every locked V1 contract name exactly once

- Start one centrally owned debug session
   - Expected: declaration_count(service, "pub class DebugServiceV1:") equals `1`
   - Expected: declaration_count(contracts, "pub struct DebugWireV1:") equals `1`
   - Expected: declaration_count(contracts, "pub struct DebugSessionId:") equals `1`
   - Expected: declaration_count(contracts, "pub struct DebugTargetGraphV1:") equals `1`
   - Expected: declaration_count(contracts, "pub struct DebugCapabilityV1:") equals `1`
   - Expected: declaration_count(contracts, "pub struct DebugEventV1:") equals `1`
   - Expected: declaration_count(contracts, "pub struct DebugReceiptV1:") equals `1`
   - Expected: declaration_count(contracts, "pub struct DebugPolicyV1:") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Start one centrally owned debug session")
val contracts = file_read(CONTRACTS_V1)
val service = file_read(SERVICE_V1)
expect(declaration_count(service, "pub class DebugServiceV1:")).to_equal(1)
expect(declaration_count(contracts, "pub struct DebugWireV1:")).to_equal(1)
expect(declaration_count(contracts, "pub struct DebugSessionId:")).to_equal(1)
expect(declaration_count(contracts, "pub struct DebugTargetGraphV1:")).to_equal(1)
expect(declaration_count(contracts, "pub struct DebugCapabilityV1:")).to_equal(1)
expect(declaration_count(contracts, "pub struct DebugEventV1:")).to_equal(1)
expect(declaration_count(contracts, "pub struct DebugReceiptV1:")).to_equal(1)
expect(declaration_count(contracts, "pub struct DebugPolicyV1:")).to_equal(1)
```

</details>

#### should accept V1 peers and reject unsupported or malformed majors structurally

- Start one centrally owned debug session
   - Expected: exact.accepted is true
   - Expected: exact.local_major equals `1`
   - Expected: additive.accepted is true
   - Expected: additive.peer_major equals `1`
   - Expected: future.accepted is false
   - Expected: future.peer_major equals `2`
   - Expected: future.reason equals `unsupported debug wire major`
   - Expected: malformed.accepted is false
   - Expected: malformed.peer_major equals `-1`
   - Expected: malformed.reason equals `invalid debug wire version`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Start one centrally owned debug session")
val exact = debug_wire_negotiate_v1("debug-wire-v1")
val additive = debug_wire_negotiate_v1("debug-wire-v1.7")
val future = debug_wire_negotiate_v1("debug-wire-v2")
val malformed = debug_wire_negotiate_v1("wire-latest")
expect(exact.accepted).to_equal(true)
expect(exact.local_major).to_equal(1)
expect(additive.accepted).to_equal(true)
expect(additive.peer_major).to_equal(1)
expect(future.accepted).to_equal(false)
expect(future.peer_major).to_equal(2)
expect(future.reason).to_equal("unsupported debug wire major")
expect(malformed.accepted).to_equal(false)
expect(malformed.peer_major).to_equal(-1)
expect(malformed.reason).to_equal("invalid debug wire version")
```

</details>

#### should keep support verification and perturbation as independent facts

- Choose the cheapest decisive observation


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Choose the cheapest decisive observation")
val contracts = file_read(CONTRACTS_V1)
val capability = between(contracts, "pub struct DebugCapabilityV1:", "pub struct DebugTargetNodeV1:")
expect(capability).to_contain("support: CapLevel")
expect(capability).to_contain("verification: DebugVerificationV1")
expect(capability).to_contain("perturbation: DebugPerturbationV1")
expect(contracts).to_contain("LiveVerified")
expect(contracts).to_contain("FixtureVerified")
expect(contracts).to_contain("Unverified")
expect(contracts).to_contain("Blocked")
expect(contracts).to_contain("Passive")
expect(contracts).to_contain("Cooperative")
expect(contracts).to_contain("Stopping")
expect(contracts).to_contain("Mutating")
```

</details>

#### should keep the root operation surface small and version domain extension

- Choose the cheapest decisive observation
   - Expected: roots does not contain `Attach`
   - Expected: roots does not contain `Sql`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Choose the cheapest decisive observation")
val contracts = file_read(CONTRACTS_V1)
val roots = between(contracts, "pub enum DebugRootOperationV1:", "pub struct DebugSessionId:")
expect(roots).to_contain("Observe")
expect(roots).to_contain("Inspect")
expect(roots).to_contain("Control")
expect(roots).to_contain("Probe")
expect(roots).to_contain("Profile")
expect(roots).to_contain("Evidence")
expect(roots).to_contain("Domain")
expect(roots.contains("Attach")).to_equal(false)
expect(roots.contains("Sql")).to_equal(false)
```

</details>

### REQ-001/009/010: central session policy and receipts

#### should make DebugServiceV1 the central mutable owner

- Start one centrally owned debug session


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Start one centrally owned debug session")
val service = file_read(SERVICE_V1)
val owner = between(service, "pub class DebugServiceV1:", "    static fn create()")
expect(owner).to_contain("sessions: [DebugSessionRecordV1]")
expect(owner).to_contain("receipts: [DebugReceiptV1]")
expect(service).to_contain("me open_session(")
expect(service).to_contain("me add_target(")
expect(service).to_contain("me authorize(")
expect(service).to_contain("me close_session(")
```

</details>

#### should reject anonymous builds and return session IDs to clients

- Start one centrally owned debug session


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Start one centrally owned debug session")
val service = file_read(SERVICE_V1)
val opening = between(service, "    me open_session(", "    me open_observe_session(")
expect(opening).to_contain("Result<DebugSessionId, text>")
expect(opening).to_contain('if build_id.trim() == ""')
expect(opening).to_contain("debug session requires an exact build id")
expect(opening).to_contain("DebugSessionId(value:")
expect(opening).to_contain("build_id: build_id")
```

</details>

#### should authorize before action and emit build-bound receipts

- Capture receipted evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture receipted evidence")
val service = file_read(SERVICE_V1)
val authorization = between(service, "    me authorize(", "    me close_session(")
expect(authorization).to_contain("policy.allow_control")
expect(authorization).to_contain("policy.allow_probe")
expect(authorization).to_contain("policy.allow_profile")
expect(authorization).to_contain("policy.allow_evidence")
expect(authorization).to_contain("not policy.allow_mutation")
expect(service).to_contain("build_id = self.sessions[idx].build_id")
expect(service).to_contain("execution_changed: execution_changed")
expect(service).to_contain("self.receipts.push(receipt)")
```

</details>

### REQ-003/005/007: topology provenance and additive migration

#### should bind target topology and events to sessions and exact builds

- Discover the real target graph


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Discover the real target graph")
val contracts = file_read(CONTRACTS_V1)
val graph = between(contracts, "pub struct DebugTargetGraphV1:", "pub struct DebugEventV1:")
val event = between(contracts, "pub struct DebugEventV1:", "pub struct DebugPolicyV1:")
expect(graph).to_contain("session_id: DebugSessionId")
expect(graph).to_contain("build_id: text")
expect(graph).to_contain("nodes: [DebugTargetNodeV1]")
expect(graph).to_contain("edges: [DebugTargetEdgeV1]")
expect(event).to_contain("session_id: DebugSessionId")
expect(event).to_contain("build_id: text")
expect(event).to_contain("source_anchor: text")
expect(event).to_contain("symbol_id: text")
```

</details>

#### should retain causality privacy typed payload and observed-or-caused provenance

- Capture receipted evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture receipted evidence")
val contracts = file_read(CONTRACTS_V1)
val event = between(contracts, "pub struct DebugEventV1:", "pub struct DebugPolicyV1:")
expect(event).to_contain("trace_id: text")
expect(event).to_contain("task_id: text")
expect(event).to_contain("transaction_id: text")
expect(event).to_contain("query_id: text")
expect(event).to_contain("privacy_label: text")
expect(event).to_contain("payload_type: text")
expect(event).to_contain("provenance: DebugProvenanceV1")
expect(contracts).to_contain("Observed")
expect(contracts).to_contain("Caused")
```

</details>

#### should add V1 contracts without redefining legacy backend traits

- Clean up and record reusable knowledge
   - Expected: contracts does not contain `trait DebugBackend`
   - Expected: contracts does not contain `trait DebugTarget`
   - Expected: service does not contain `trait DebugBackend`
   - Expected: service does not contain `trait DebugTarget`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Clean up and record reusable knowledge")
val contracts = file_read(CONTRACTS_V1)
val service = file_read(SERVICE_V1)
expect(contracts.contains("trait DebugBackend")).to_equal(false)
expect(contracts.contains("trait DebugTarget")).to_equal(false)
expect(service.contains("trait DebugBackend")).to_equal(false)
expect(service.contains("trait DebugTarget")).to_equal(false)
expect(service).to_contain("Central owner for V1 debug sessions")
```

</details>

### Wave 0 runtime behavior

#### should isolate session IDs builds and receipt streams

- Start one centrally owned debug session
   - Expected: first.value == second.value is false
   - Expected: service.session_count() equals `2`
   - Expected: first_receipts.len() equals `1`
   - Expected: second_receipts.len() equals `1`
   - Expected: first_receipts[0].build_id equals `build-a`
   - Expected: second_receipts[0].build_id equals `build-b`
   - Expected: first_receipts[0].session_id.value equals `first.value`
   - Expected: second_receipts[0].session_id.value equals `second.value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Start one centrally owned debug session")
val service = DebugServiceV1.create()
val first = require_session(service.open_observe_session("build-a"))
val second = require_session(service.open_observe_session("build-b"))
expect(first.value == second.value).to_equal(false)
expect(service.session_count()).to_equal(2)
val first_receipts = service.receipts_for(first)
val second_receipts = service.receipts_for(second)
expect(first_receipts.len()).to_equal(1)
expect(second_receipts.len()).to_equal(1)
expect(first_receipts[0].build_id).to_equal("build-a")
expect(second_receipts[0].build_id).to_equal("build-b")
expect(first_receipts[0].session_id.value).to_equal(first.value)
expect(second_receipts[0].session_id.value).to_equal(second.value)
```

</details>

#### should deny mutation even when development control is enabled

- Choose the cheapest decisive observation
   - Expected: receipt.allowed is false
   - Expected: receipt.execution_changed is false
   - Expected: receipt.reason equals `mutation denied by policy`
   - Expected: receipt.build_id equals `build-policy`
   - Expected: receipt.perturbation == DebugPerturbationV1.Mutating is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Choose the cheapest decisive observation")
val service = DebugServiceV1.create()
val session_id = require_session(service.open_session("build-policy", debug_policy_development_v1()))
val receipt = service.authorize(
    session_id,
    DebugRootOperationV1.Control,
    DebugPerturbationV1.Mutating,
    "memory.write",
)
expect(receipt.allowed).to_equal(false)
expect(receipt.execution_changed).to_equal(false)
expect(receipt.reason).to_equal("mutation denied by policy")
expect(receipt.build_id).to_equal("build-policy")
expect(receipt.perturbation == DebugPerturbationV1.Mutating).to_equal(true)
```

</details>

#### should accept only edges whose endpoints exist in the same session

- Discover the real target graph
   - Expected: graph.build_id equals `build-graph`
   - Expected: graph.nodes.len() equals `2`
   - Expected: graph.edges.len() equals `1`
   - Expected: graph.edges[0].boundary equals `process-task`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Discover the real target graph")
val service = DebugServiceV1.create()
val session_id = require_session(service.open_observe_session("build-graph"))
val host = DebugTargetNodeV1(target_id: "host", parent_target_id: "", kind: "host", label: "Host")
val worker = DebugTargetNodeV1(target_id: "worker", parent_target_id: "host", kind: "worker", label: "Worker")
match service.add_target(session_id, host, native_capability("host")):
    case Ok(_): pass_do_nothing("host added")
    case Err(reason): fail("host target rejected: {reason}")
match service.add_target(session_id, worker, native_capability("worker")):
    case Ok(_): pass_do_nothing("worker added")
    case Err(reason): fail("worker target rejected: {reason}")
val real_edge = DebugTargetEdgeV1(
    from_target_id: "host",
    to_target_id: "worker",
    kind: DebugTargetEdgeKindV1.Owns,
    boundary: "process-task",
)
match service.add_edge(session_id, real_edge):
    case Ok(_): pass_do_nothing("real edge added")
    case Err(reason): fail("real edge rejected: {reason}")
val fabricated_edge = DebugTargetEdgeV1(
    from_target_id: "host",
    to_target_id: "missing",
    kind: DebugTargetEdgeKindV1.Boundary,
    boundary: "fabricated",
)
match service.add_edge(session_id, fabricated_edge):
    case Ok(_): fail("edge with a missing endpoint was accepted")
    case Err(reason): expect(reason).to_equal("debug edge endpoints must exist")
val graph = require_graph(service.graph(session_id))
expect(graph.build_id).to_equal("build-graph")
expect(graph.nodes.len()).to_equal(2)
expect(graph.edges.len()).to_equal(1)
expect(graph.edges[0].boundary).to_equal("process-task")
```

</details>

#### should close idempotently and deny later action without changing execution

- Clean up and record reusable knowledge
   - Expected: service.session_count() equals `0`
   - Expected: denied.allowed is false
   - Expected: denied.execution_changed is false
   - Expected: denied.reason equals `debug session is closed`
   - Expected: denied.build_id equals `build-close`
   - Expected: receipts.len() equals `3`
   - Expected: receipts[1].action equals `session.close`
   - Expected: receipts[1].execution_changed is false
   - Expected: receipts[2].outcome equals `denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Clean up and record reusable knowledge")
val service = DebugServiceV1.create()
val session_id = require_session(service.open_observe_session("build-close"))
match service.close_session(session_id):
    case Ok(_): pass_do_nothing("session closed")
    case Err(reason): fail("close rejected: {reason}")
match service.close_session(session_id):
    case Ok(_): pass_do_nothing("repeat close is idempotent")
    case Err(reason): fail("repeat close rejected: {reason}")
expect(service.session_count()).to_equal(0)
val denied = service.authorize(
    session_id,
    DebugRootOperationV1.Evidence,
    DebugPerturbationV1.Passive,
    "evidence.capture",
)
expect(denied.allowed).to_equal(false)
expect(denied.execution_changed).to_equal(false)
expect(denied.reason).to_equal("debug session is closed")
expect(denied.build_id).to_equal("build-close")
val receipts = service.receipts_for(session_id)
expect(receipts.len()).to_equal(3)
expect(receipts[1].action).to_equal("session.close")
expect(receipts[1].execution_changed).to_equal(false)
expect(receipts[2].outcome).to_equal("denied")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `[Unified debugging requirements](doc/02_requirements/feature/simple_unified_debugging_evidence.md)`
- **Plan:** `[System-test plan](doc/03_plan/sys_test/simple_unified_debugging_evidence.md)`
- **Design:** `[Unified detail design](doc/05_design/simple_unified_debugging_evidence.md)`
- **Research:** `[Unified debugging research](doc/01_research/app/tools/simple_unified_debugging_evidence_2026-08-14.md)`


</details>
