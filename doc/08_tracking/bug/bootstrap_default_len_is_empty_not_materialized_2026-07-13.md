# Bootstrap default `Len.is_empty` is not materialized
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

Strict stage2 linking retains calls to the default `Len.is_empty` trait method
without materializing its body. The current failure came from
`SdnBackendImpl.process_module`; `/usr/bin/ld` reported undefined
`compiler_rust__lib__std__src__core__traits__Len_dot_is_empty`.

The immediate bootstrap path uses the collection's existing `len()` method.
The compiler still needs a focused regression and an owner fix that retains or
specializes reachable default trait methods in native entry closures.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
