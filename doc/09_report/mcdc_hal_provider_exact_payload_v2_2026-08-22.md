# rt(hal) provider exact payload V2 evidence — 2026-08-22

Revision-under-test adds the additive `HALREQ2B` / `HALRES2B` frame.  V1 and
the scalar V2 frame are unchanged.  The byte frame admits only producible
`EnvironmentGet` (102), typed `FileRead` (1001), and typed `StreamRead` (1004)
observations.  Providers receive already-captured caller-owned bytes; they do
not consult ambient environment or storage.

## Correctness and safety

`sh scripts/check/check-hal-provider-workers-v1.shs` passed.  C and Rust emitted
identical normalized receipts after provider identity removal for all three
operations.  The receipt retained all eight fixture bytes, structured error
`environment:17:23`, and trace identity/cursor/length exactly.  Payload length
above capacity, capacity above 32, nonzero unused padding, an unbound trace,
and an unadmitted operation all failed closed without a result frame.

Both native workers retain fixed 512-byte stack frames and contain no direct
heap operation.  The Pure Simple source implements the same 19-field request,
23-field result, operation allowlist, signed full-word transport, canonical
padding check, and exact receipt.  A Pure native receipt remains unavailable
because the deployed Pure Simple compiler is inadmissible; it was not replaced
with the Rust seed.

## Performance and memory

Persistent-session comparison, 20,000 reset/request/result cycles, same O3
workers and host:

| provider | scalar V2 baseline | exact-byte V2 | peak RSS baseline/after |
|---|---:|---:|---:|
| C | 1.35 s | 1.89 s | 1,024 / 1,024 KiB |
| Rust | 1.33 s | 1.91 s | 1,792 / 1,792 KiB |

The additional time is bounded linear parsing/serialization of eight real
payload bytes plus structured error fields rather than scalar metadata.  It
adds no allocation, copying remains one fixed inline receipt, locality remains
stack-contiguous, and dispatch adds two prefix checks.  Complexity is O(frame)
with a hard 512-byte frame and 32-byte payload cap; no payload-sized dynamic
state exists.  The optimizer was not run because the only deployed Pure Simple
compiler is inadmissible.
