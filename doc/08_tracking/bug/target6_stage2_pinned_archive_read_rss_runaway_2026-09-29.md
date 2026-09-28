# Stage-2 pinned archive read RSS runaway (2026-09-29)

Status: focused Stage-2 native repro now passes; production memory/performance
qualification remains open. No current-source Stage-4 result is claimed.

While replacing the cold publisher's bounded CAS member check with
`pinned_archive_open_verified_v1` and
`interface_action_archive_decode_v1`, the
`cold_hir_compact_output_index_spec.spl` native worker stopped after its first
three scenarios. The process was still running at 99.9% CPU after about 58
seconds, with 15,864,992 KiB RSS. Its open archive descriptor referred to a
542-byte regular CAS blob. The process was terminated with SIGTERM; it did not
produce a test verdict for that run.

The root-relative CAS path correction got the worker past the earlier
`archive-open-invalid` rejection. The excessive allocation occurred after the
archive opened, somewhere in pinned digest/member reading or its native
future/mapping path. That location is an inference, not a proven cause.

The production change was reverted. Cold publication retains its bounded
whole-blob/member verification and now shares a pure semantic payload decoder
with warm admission. A future fix should isolate the pinned reader with a
bounded native probe, inspect its size/future/mapping transport, and compare
RSS and elapsed time before using it in cold publication.

## Follow-up: synchronous read and digest types (2026-09-29)

For a 542-byte archive, `FileReadPolicyV1.auto_map` selects the buffered path:
its mapping threshold is 65,536 bytes. The synchronous file-view API was
wrapping an already completed typed result in `Future.from_value` and passing
it through the global async runtime, whose `TaskResult.value` is text. It now
returns the synchronous result directly. A no-stub Stage-2 native spec reads
the 38-byte hello fixture exactly and rejects an out-of-range read: 2 examples,
0 failures, 0.00 s reported by `/usr/bin/time`, 3,224 KiB peak RSS under a
2 GiB virtual-memory limit.

The pinned reader also compared `sha256_bytes([u8])` to hex text digests and
returned those digest bytes from a `text?` function. Both sites now use
`sha256_u8_hex([u8])`. These were concrete type errors, but this evidence does
not isolate which one caused the earlier 15 GiB growth.

An attempted pinned archive integration probe compiled 332 no-stub units and
linked, but aborted on `unwrap(None)` before reporting a pinned-read verdict
(1.38 s, 4,060 KiB peak RSS). The new integration scenario was removed; its
receipt/load setup needs a guarded diagnostic before the pinned path can be
qualified. Do not re-enable it in cold publication or claim a memory win until
a native archive probe passes and paired time/RSS samples are recorded.

## Follow-up: guarded archive receipt (2026-09-29)

The earlier integration probe used a module entry's action digest to load an
archive published under its SCC aggregate digest, then unwrapped the absent
receipt. A guarded fixture now reads the actual batch mapping and receipt.
It opens and reads the same 542-byte archive through the pinned capability:
8 native examples pass, 0 failures, 8,236 KiB peak RSS. The pinned read is
usable in this focused case. Replacing the cold publisher's whole-blob path
did not meet the normalized time/RSS rule beyond noise, so that trial was
reverted. See
`doc/09_report/compiler/target6_pinned_archive_native_and_cold_publisher_diagnostic_2026-09-29.md`.

## Follow-up: bounded digest trial rejected (2026-09-29)

A 64 KiB buffered descriptor read plus `sha256_stream_v1_update` compiled in
the no-stub Stage-2 native capsule (2 changed units, 330 reused), but the
guarded 542-byte archive scenario failed while the other seven scenarios
passed. Under a 2 GiB virtual-memory limit, the diagnostic worker finished
in 0.13 s at 8,464–8,472 KiB peak RSS. The bounded change and temporary
diagnostic prints were reverted; the known-passing whole-archive digest path
remains in production.

The admitted archive digest was `f0dbda59…fcc8ca`, confirmed by `sha256sum`
on the CAS file. A diagnostic `cas_get(...).bytes()` conversion produced
542 bytes whose one-shot `sha256_u8_hex` was `c07df267…c3c5dc` instead.
That text conversion is therefore unsuitable as a binary archive oracle.
Independently, `sha256_stream_v1_update` over those *same converted bytes*
produced `2fc603c0…192085`, disagreeing with the one-shot digest. The stream
reported `total_bytes=542` and `block_len=30`, so the mismatch is not explained
by a missing byte count. The native stream implementation or its call boundary
needs a known-vector, multi-block parity test; the existing partition test
only pins the empty digest and compares partitions against each other.

Next: test incremental SHA-256 against external known digests at block
boundaries and over several chunks in the no-stub native binary; correct that
path, then rerun pinned archive admission with descriptor bytes. Only after
that passes, compare paired time and peak RSS on a realistically large CAS
archive against the existing path and apply the normalized time/RSS gate.
