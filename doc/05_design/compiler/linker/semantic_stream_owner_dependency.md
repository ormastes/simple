# Canonical semantic stream owner dependency

Date: 2026-10-04. Research base: release `d8680fe6ec21`.
Trace: existing REQ-CSM-003/006; item4 Phase 4 compiler dependency.

## Contract

The frozen canonical byte format is unchanged. One mutable stream owns SHA,
byte/item/work counters, root count, frame stack, sticky error and finished
state. Every mutating or transitively mutating helper becomes a `me` method.
Public method names retain their existing semantic_canonical_*_v1 spelling,
with the explicit stream argument removed. Constructors, pure encoders and
read-only observers stay free functions. There is no compatibility shim that
silently mutates a copied value.

The byte builder owns tag framing through a mutable append_tag operation.
Container state extracted from the frame array must be written back after
changes. Closing a frame attaches its complete encoded bytes to its parent or
the root through the same owner, preserving map/set ordering and duplicate
rejection. Rejections preserve the first error; later calls cannot make a
failed or finished stream publish another digest.

Precharge checks the entire prospective byte/item/work operation before
advancing counters. Successful operations accumulate counters on the caller's
owner. Finalization charges its work once, validates closed containers and one
root, then finalizes the retained SHA owner. A second finish fails on that same
owner. Constructor headers and all existing digest vectors remain stable.

## Production reachability

The earlier defect report incorrectly named the declaration issuer as a live
caller. At this base it has comments only, no stream imports or invocation, and
explicitly rejects installation without five live capability owners. Preserve
that authority boundary. This repair makes the primitive correct; it does not
activate a compiler cache issuer or provide provider-manifest trust.

## Concrete acceptance

| Obligation | Oracle |
|---|---|
| Header/domain/schema framing | Existing independent Begin01 scalar digest and header byte count |
| Persistent budgets | Original owner's byte/item/work counters after consecutive nested writes; exact boundary and one-over rejection |
| Sticky error | Trigger two different errors; first remains observable, later mutation leaves counters unchanged |
| Parent frame propagation | Close nested containers and inspect parent/root state; complete existing nested digest vectors |
| Root arity | Second root rejects on original owner |
| Finalize once | First finish succeeds, second rejects on same owner without charging again |
| Late mutation | Writes after successful finish cannot publish a second digest |
| Format compatibility | Existing scalar/UTF-8/map/set/record/variant/owner-set suites retain exact expectations |

The canonical spec stays at
`test/01_unit/compiler/cache/semantic_canonical_stream_v1_spec.spl` and uses
real step assertions. Execution requires an admitted self-hosted runtime:
`<runtime> test <spec> --native`. Regenerate its manual using
`<runtime> spipe-docgen <spec> --output doc/06_spec --no-index`, requiring zero
stubs. Core/lib/MCP checks, native smoke and coverage are additional gates.

State: implementation and four owner-state scenarios authored; two independent
core source reviews report P0=0/P1=0. Native execution, compilation, docgen and
coverage remain UNRUN; source review cannot grant Phase 4 PASS.
