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
