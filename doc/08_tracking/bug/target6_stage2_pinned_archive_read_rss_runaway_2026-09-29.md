# Stage-2 pinned archive read RSS runaway (2026-09-29)

Status: open; observed only in the isolated no-stub Stage-2 native test worker
linked against the hosted runtime archive. No current-source Stage-4 result is
claimed.

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
