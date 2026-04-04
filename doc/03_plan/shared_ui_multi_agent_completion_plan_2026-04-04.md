# Shared UI Multi-Agent Completion Plan

**Date:** 2026-04-04  
**Status:** Draft  
**Scope:** Complete the shared UI feature so it moves from “real shared test surface” to a fully supported, explicitly scoped shared UI contract across supported surfaces.

## 1. Goal

Move shared UI testing from:
- a real shared HTTP-oriented test surface

to:
- a complete shared UI contract with proof-backed multi-surface behavior

Current state is strong enough to claim:
- shared testing across the web backend and TUI-web proxy

Current state is not strong enough to claim:
- one finished unified UI layer across all UI surfaces

This plan does **not** assume all UI surfaces are one system.
It starts by defining exactly what “shared UI” means.

## 2. Completion Criteria

The feature is complete when:

1. There is one explicit shared UI contract.
2. Supported surfaces are named precisely.
3. Each supported surface passes the same contract suite.
4. Surface-specific deviations are documented and intentional.
5. The shared test client is authoritative, not only a convenience wrapper.
6. README and docs say “shared UI contract across these supported surfaces”, not vague “unified UI”.

## 3. Likely Support Classes

### Stable Shared Surfaces

- web backend
- TUI-web proxy

### Scoped or Adapter-Only Surfaces

- native TUI if only partially bridged
- dashboard-style render adapters if only partially compatible
- any direct GUI surface without the common protocol

### Out of Scope for the Shared UI Claim

- surfaces without the common request/response contract
- pixel-only or browser-layout-specific UI validation
- terminal-emulator-specific rendering quirks

The first implementation step must freeze which surfaces belong to which class.

## 4. Multi-Agent Work Breakdown

### Agent 1: Shared UI Contract Definition

Ownership:
- source-of-truth contract and support matrix

Primary files:
- `doc/07_guide/testing/testing.md`
- shared UI docs
- `doc/report/`

Tasks:
- define the exact shared UI abstraction:
  - widget tree model
  - event model
  - request/response model
  - state/session model
  - rendering-independent assertions
- define what is in scope:
  - actions
  - text/value assertions
  - visibility
  - layout metadata if actually shared
  - focus/selection/navigation
- define what is explicitly out of scope:
  - pixel-perfect rendering
  - CSS/browser layout fidelity
  - terminal emulator quirks
- build a support matrix:
  - surface
  - protocol support
  - interaction support
  - assertion support
  - proof status
  - known gaps

Deliverables:
- shared UI contract doc
- support matrix

Acceptance:
- the rest of the implementation works against one fixed contract, not assumptions

### Agent 2: Shared Protocol and Core Handler Parity

Ownership:
- common protocol and shared handler

Primary files:
- shared UI test client modules
- shared request handler modules
- protocol types
- request parsing / response formatting code

Tasks:
- audit the common protocol:
  - command names
  - input schema
  - response schema
  - error schema
- make the protocol versioned and explicit if not already
- unify error responses across supported surfaces
- close gaps where one surface returns shape A and another returns shape B
- ensure stable node IDs, selectors, or action handles

Acceptance:
- one protocol contract
- one error model
- the same request yields the same semantic result shape across supported surfaces

### Agent 3: Surface Adapter Parity

Ownership:
- per-surface adapters only

Primary files:
- web backend integration
- TUI-web proxy integration
- any other shared-protocol adapters

Tasks:
- compare adapter behavior against the shared contract
- classify each operation as:
  - implemented
  - intentionally unsupported
  - accidentally divergent
- close accidental divergences in:
  - focus handling
  - click/submit behavior
  - text/value extraction
  - navigation/event propagation

Acceptance:
- supported surfaces implement the same semantic operations even if rendering differs

### Agent 4: Widget and State Semantics

Ownership:
- widget tree and state-model consistency

Primary files:
- common widget/session/tree modules
- adapter translation layers

Tasks:
- define canonical semantics for:
  - visible/hidden
  - enabled/disabled
  - focused
  - selected
  - text/value/content
  - container/child relations
- ensure both supported surfaces expose equivalent widget-state information through the shared protocol
- normalize transient state reporting where surfaces drift

Acceptance:
- assertions target shared semantics, not surface-specific quirks

### Agent 5: Event Model and Interaction Fidelity

Ownership:
- shared interaction semantics

Primary files:
- event dispatch
- input translation
- action routing
- session interaction code

Tasks:
- unify semantics for:
  - click
  - input text
  - submit
  - keyboard navigation
  - selection changes
  - scroll if it is in scope
- define which interactions are mandatory across shared surfaces
- define which remain surface-specific extensions
- stabilize event ordering where races exist

Acceptance:
- the same interaction script can run against both supported surfaces and mean the same thing

### Agent 6: Test Matrix and Cross-Surface Proof

Ownership:
- contract suite and authoritative proof

Primary files:
- `test/feature/`
- `test/integration/`
- shared UI specs

Tasks:
- build one shared contract suite covering:
  - render tree retrieval
  - widget lookup
  - text assertions
  - action dispatch
  - focus transitions
  - form entry and submission
  - state mutation after events
- run the same suite against each supported surface
- separate:
  - contract tests
  - surface adapter tests
  - transport tests
  - rendering-specific tests
- add negative tests:
  - unsupported action returns explicit capability error
  - invalid selector returns deterministic error
  - stale session invalidation is consistent

Acceptance:
- each supported surface passes the same contract suite
- deviations are explicit and intentional

### Agent 7: Performance, Session, and Lifecycle

Ownership:
- non-functional closure for shared UI

Primary files:
- session handling
- server lifecycle
- request handling
- caching/state persistence if present

Tasks:
- define lifecycle semantics:
  - session create
  - session reuse
  - state reset
  - teardown
- define latency targets for shared UI operations
- prevent protocol drift caused by per-surface session handling
- ensure repeated tests are stable and isolated
- add concurrency/isolation tests if sessions are parallel or multi-client

Acceptance:
- shared UI tests are stable across repeated runs
- session semantics are documented and testable

### Agent 8: Public Wording and Scope Control

Ownership:
- docs only after proof exists

Primary files:
- `README.md`
- `doc/report/unique_features.md`
- testing guide docs

Tasks:
- replace vague “shared UI” language with exact wording:
  - which surfaces
  - what is shared
  - what is not
- publish the support matrix
- classify surfaces as:
  - shared-contract stable
  - shared-contract supported with qualifiers
  - adapter-only
  - out of scope

Acceptance:
- public wording is derivable from the support matrix

## 5. Recommended Execution Order

1. Agent 1 defines the contract and scope.
2. Agents 2, 3, 4, and 5 work in parallel.
3. Agent 6 builds the cross-surface proof suite after the contract stabilizes.
4. Agent 7 hardens lifecycle and performance once behavior is stable.
5. Agent 8 updates docs last.
6. Main agent integrates and runs final verification.

## 6. Critical Early Decisions

These must be fixed before implementation spreads:

1. Which surfaces are actually part of the shared claim?
2. Is the claim about:
   - shared test protocol only
   - shared widget semantics
   - or a full shared application model?
3. Are layout assertions in scope, or only semantic UI assertions?
4. Is native TUI in scope, or only TUI-web?
5. What is the stable selector model:
   - ID-based
   - text-based
   - structural path
   - mixed?

If these are not fixed early, the implementation will drift.

## 7. Recommended Contract Test Categories

### Tree / Read

- fetch UI tree
- stable node identity
- text/value visibility

### Actions

- click
- input
- submit
- command dispatch

### Focus / State

- focus movement
- enabled/disabled
- selection state
- transient state updates

### Forms

- entry
- validation
- submit result
- error display

### Navigation

- route/view switching
- back/forward or equivalent view state
- panel/dialog open-close semantics

### Errors

- invalid selector
- unsupported action
- stale session
- malformed request

## 8. Definition of Done

Shared UI is complete when:

- there is one documented shared UI contract
- supported surfaces are named and limited
- each supported surface passes the same contract suite
- surface-specific differences are explicit
- session and event semantics are deterministic
- docs stop implying a broader unified UI layer than the repo actually has

## 9. Recommended Real Agent Assignment

- Agent A: shared UI contract and support matrix
- Agent B: protocol/core handler parity
- Agent C: web adapter parity
- Agent D: TUI-web adapter parity
- Agent E: widget/state semantics
- Agent F: event model and interaction fidelity
- Agent G: contract suite and cross-surface proof
- Main agent: lifecycle/performance integration, docs, final verification

## 10. Immediate Next Steps

1. Freeze the list of surfaces in scope.
2. Freeze the protocol schema and error model.
3. Build one contract suite that must pass on both web and TUI-web.
4. Only after that decide whether the feature remains:
   - `shared UI testing surface`
   or can become:
   - `shared UI contract across supported surfaces`
