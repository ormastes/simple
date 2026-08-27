# RT/HAL typed-exit protocol

`@rt(hal, c|rust)` exit capture is a typed MIR operation. It never transports a
native address, object bytes, tagged runtime value, or pseudo-address.

## V3 sealed-plan boundary

The public V2 entry is quarantined (`RTHAL-E-LEGACY-V2-QUARANTINED`). A direct
V3 caller is also rejected before partial installation
(`RTHAL-E-EXIT-SEAL-REQUIRED`). The only live preparation route is the
compiler-owned staged V3 owner: it derives the canonical full-plan identity,
installs the fixed arena/schema/controller catalog, seals it, and then admits
the plan. Same-rank plans with different identities cannot reuse a Ready
catalog. This prevents a reduced plan from being substituted after compiler
semantic admission.

## Envelope

`MirInstKind.RtHalExitCapture` carries the operation ID, selected foreign
providers, exit kind, optional typed MIR operand, its MIR type, and a canonical
descriptor. Exit-kind codes are fixed: `1 Return`, `2 Error`, `3 Throw`,
`4 Resume`, `5 Abort`; `0` is rejected.

The descriptor grammar is owned by `exact_type_descriptor_parser`: primitives
use `v2;<name>`; array, tuple, and result children are decimal-length framed.
A type without a finite canonical snapshot is represented by an empty
descriptor and fails closed. V3 adds canonical operation and input binding
before comparison; it does not invent a pointer, struct, dictionary, or opaque
descriptor.

## Ownership and lifecycle

The cold controller installs `RtHalExactExitArena`, registers each canonical
descriptor in its fixed type table, registers a stable schema ID to the sealed
output/error/effect dense-ID triple, then seals it. A generated codec receives
the stable schema ID and owner-local writer token; the runtime resolves the
three dense IDs only after sealing. It invokes bounded `begin`, append, and
`finish` operations; no call grows storage or retains a raw runtime value. The
writer token is exclusive and aborts incomplete payloads. Capture precedes the
original terminator; controller drain occurs only after producer quiescence.

Each transcript event is 16 little-endian bytes (`i64 tag`, `i64 argument`).
The cold controller copies a completed capture into a self-contained typed V3
request/receipt arena and uses the exact encode-submit/join/readmit flow.
Output, error, and effect descriptors are separately admitted. Pure Simple
executes an irreversible effect once; C/Rust receive replay material and never
own that physical effect.

## Backend rule

Backends lower capture only with a compiler-generated, type-directed canonical
codec plan that has registered descriptor IDs and a sealed V3 operation map.
They reject a capture without a descriptor, codec plan, sealed type-table
mapping, or canonical plan identity. Raw `void* + sizeof`, aggregate
pseudo-addresses, padding, pointer identity, and a foreign-only fallback are
not valid fallbacks.

## Evidence boundary

The compiler-stage lifecycle, V3 provenance, exact schema/wire ownership, and
provider protocol specs are source contracts until run with an admitted
self-hosted runtime. A V2/V3 manual or fixture does not prove live foreign
provider parity, environment interaction, allocation behavior, or release
admission.
