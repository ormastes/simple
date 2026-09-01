# Pure HAL worker fixed-frame evidence — 2026-08-22

The Pure Simple provider now mirrors the C/Rust fixed-storage protocol shape.
Initialization owns three 512-byte arenas (buffered stdin, complete request,
response), for 1,536 bytes total. The sealed loop scans each input byte a
bounded number of times, parses numeric fields in place, and formats decimal
fields directly into the response arena. Complexity is O(frame bytes), storage
is O(1), and no dynamic array, text construction, split, substring, or
read/write-line API is reachable after initialization.

`scripts/check/check-hal-pure-worker-noalloc-source.shs` is the focused retained
gate. It checks the allocation/source closure, all three request prefixes,
reset framing, numeric/arena bounds, exact cleanup ownership, valid model rows,
and malformed/oversized fail-closed rows. The host model is deliberately
reported as a model rather than native timing.

Native Pure execution, peak RSS, allocation tracing, and OptimizerPlugin output
remain unavailable because the deployed self-hosted compiler is inadmissible.
The Rust bootstrap seed was not substituted. Existing native C/Rust worker
evidence remains the comparison baseline; a source-matched Pure binary is still
required before claiming measured Pure parity.
