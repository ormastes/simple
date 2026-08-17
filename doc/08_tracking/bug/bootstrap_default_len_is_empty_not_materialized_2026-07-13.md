# Bootstrap default `Len.is_empty` is not materialized

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

Strict stage2 linking retains calls to the default `Len.is_empty` trait method
without materializing its body. The current failure came from
`SdnBackendImpl.process_module`; `/usr/bin/ld` reported undefined
`compiler_rust__lib__std__src__core__traits__Len_dot_is_empty`.

The immediate bootstrap path uses the collection's existing `len()` method.
The compiler still needs a focused regression and an owner fix that retains or
specializes reachable default trait methods in native entry closures.
