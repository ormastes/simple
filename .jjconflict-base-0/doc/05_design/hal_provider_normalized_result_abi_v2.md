# Normalized HAL Provider Result ABI V2

## Scope and compatibility

V2 is additive. `HalProviderResultV1`, `HALREQ1`, and `HALRES1` retain their
layout and behavior. V2 closes the digest-only comparison gap by carrying the
normalized result itself. The parent remains the sole environment-observation
and commit authority; workers receive an encoded captured observation and may
only return a child-created result for validation.

## Bounded ownership

`HalProviderResultV2` is pointer-free value state. Scalar results occupy one
`i64`. Byte results occupy four inline `i64` words (32 bytes maximum) plus an
explicit length and caller-supplied capacity. Error domain/code/detail and
environment trace identity/cursor are fixed scalar fields. Construction and
comparison are O(1), require no collection traversal, and perform no payload
allocation or copy beyond the fixed four-word value copy.

Malformed lengths, capacities above 32 bytes, missing trace identity,
out-of-range cursors, inconsistent success/error state, and overflow metadata
fail closed. Comparison includes actual scalar/words, structured error, and
the exact trace identity/cursor rather than accepting digest equality.

## Typed replay wire

The additive `HALREQ2`/`HALRES2` direct-worker protocol carries a
parent-captured monotonic clock scalar, result capacity, and trace position.
Pure Simple, C, and Rust workers normalize that same observation; they do not
perform three independent physical clock reads. V1 requests remain byte-for-byte
compatible. The fixed wire ceiling remains 512 bytes.

`HALREQ2B` also admits the typed environment operation IDs for
`ProcessSpawn`, `ProcessPoll`, `ProcessKill`, `SocketOpen`, `SocketSend`,
`SocketReceive`, and `SocketClose` (`1006..1008`, `1012..1015`). The parent
executes or models each operation once, then sends its normalized result,
structured error, and exact trace cursor. Provider workers only validate and
return that fixed inline observation; replay therefore cannot repeat a process
or socket side effect. Lifecycle ordering remains parent-owned and is bound by
the exact trace identity, cursor, length, and capacity in every result.

The C and Rust worker implementations use only stack arrays and direct I/O;
the focused gate rejects heap-owning constructs. The Pure worker preserves the
existing bounded text transport pending its raw-buffer stdin owner, while the
normalized provider-result data model itself has no dynamic payload.

## Evidence (2026-08-22)

`sh scripts/check/check-hal-provider-workers-v1.shs` proves identical normalized
C/Rust scalar, byte, process-lifecycle, socket-lifecycle, structured-error, and
trace output; rejects oversize/missing-identity requests; and retains zero
direct heap calls. Measured peak RSS on the same host was unchanged: C V1/V2
1024/1024 KiB and Rust V1/V2 1792/1792 KiB.

Pure-Simple execution and optimizer evidence remain blocked by the inadmissible
self-hosted compiler; the Rust seed is deliberately not substituted.

## Sealed caller-buffer owner V3

The process-lifetime sealed owner now exposes an additive caller-buffer leaf
for every `HALREQ2B` operation: environment get (`102`), file read (`1001`),
stream read (`1004`), process spawn/poll/kill (`1006..1008`), and socket
open/send/receive/close (`1012..1015`). The parent performs the physical
operation once and loans an immutable captured byte range into the leaf. The
leaf never retains either pointer. It packs at most four little-endian words
into fixed stack wire storage, compares three isolated child-created results,
and copies the selected result into the caller-owned output only after commit
policy succeeds.

Normal mode validates the exact status/error/trace contract and performs one
bounded `memmove`, with no worker traffic. Alpha mode returns divergence and
leaves output untouched. Beta mode retains the bounded diff and commits the
configured provider. Payload capacities above 32 bytes fail closed; a future
large-buffer protocol must use the existing caller buffer as a scoped loan and
must not silently allocate an inline surrogate. Trace cursors are consumed by
one monotonic atomic owner even when comparison rejects, preventing replay.

All hot-path work is O(payload), where payload is bounded by 32 bytes. The
three-lane comparison and four-slot admission are O(1); storage is fixed and
cache-local. Initialization alone creates the isolated workers. Hot calls do
not allocate, spawn, wait for another caller, or consult the environment.

Compiler binding remains deliberately conservative. Existing environment,
file, stream, process, and socket wrappers do not share this caller-buffer ABI,
so their metadata rows remain non-rewritable. MIR substitution is enabled only
for a binding whose complete HIR signature equals its frozen direct and compare
leaf signature; adapting a heap-returning `text`/`[u8]` wrapper by symbol-only
rewrite would change ownership and error semantics and is rejected.
