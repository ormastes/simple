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

## Clock replay wire pilot

The additive `HALREQ2`/`HALRES2` direct-worker protocol carries a
parent-captured monotonic clock scalar, result capacity, and trace position.
Pure Simple, C, and Rust workers normalize that same observation; they do not
perform three independent physical clock reads. V1 requests remain byte-for-byte
compatible. The fixed wire ceiling remains 512 bytes.

The C and Rust worker implementations use only stack arrays and direct I/O;
the focused gate rejects heap-owning constructs. The Pure worker preserves the
existing bounded text transport pending its raw-buffer stdin owner, while the
normalized provider-result data model itself has no dynamic payload.

## Evidence (2026-08-22)

`sh scripts/check/check-hal-provider-workers-v1.shs` proves identical normalized
C/Rust scalar and trace output, rejects oversize/missing-identity requests, and
retains zero direct heap calls. Measured peak RSS on the same host was unchanged:
C V1/V2 1024/1024 KiB and Rust V1/V2 1792/1792 KiB.

Pure-Simple execution and optimizer evidence remain blocked by the inadmissible
self-hosted compiler; the Rust seed is deliberately not substituted.
