# Stage-2 pinned archive read RSS runaway (2026-09-29)

Status: bounded byte-feed trial rejected by paired time/RSS measurements;
the prior whole-archive digest is restored. Production memory/performance
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

## Follow-up: native stream parity and conversion diagnosis (2026-09-29)

The no-stub native unit spec now pins external SHA-256 digests for repeated
3-, 64-, 65-, 129-, and 542-byte messages and a mixed 542-byte message.
The stream passes all vectors, including a split 129-byte message: four
examples, zero failures, 3,612 KiB peak RSS. The prior suspicion of a general
stream compression defect is not supported by these tests.

The persisted archive scenario now uses `text_to_utf8_bytes` on `cas_get`
content, then checks both one-shot and streamed hashes against the admitted
digest. All eight no-stub native integration examples pass (0.14 s,
8,120 KiB peak RSS). This identifies the earlier `.bytes()` diagnostic as an
invalid way to establish the archive's UTF-8 byte identity; its repeated
calls also yielded different one-shot and streamed digests in that probe.
The production descriptor reader still needs its own bounded-chunk retest:
the passing text conversion does not prove its transport returns the same
bytes or that large archives meet the time/RSS gate. Next, isolate the
descriptor read's byte parity, then compare paired time and peak RSS on a
realistically large CAS archive against the existing path.

## Follow-up: descriptor bytes match; stream still differs (2026-09-29)

A second bounded-digest trial read 64 KiB chunks through the pinned descriptor
and fed them to `sha256_stream_v1_update`. Its no-stub native integration run
still failed only the 542-byte pinned archive scenario (8 examples, 1 failure,
0.13 s, 8,472 KiB peak RSS). A diagnostic in the same descriptor-read call
showed `sha256_u8_hex` on the returned 542-byte chunk equalled the admitted
CAS digest `f0dbda59…fcc8ca`, while the stream over that chunk returned
`67173922…39522e` with `total_bytes=542`. The descriptor transport therefore
returned hash-correct bytes in this fixture.

Copying the descriptor chunk into a newly allocated `[u8]` before streaming
did not fix admission (8 examples, 1 failure, 0.13 s, 8,120 KiB peak RSS).
The copy remained bounded at one 64 KiB chunk. Both experimental variants
and the diagnostic print were reverted, leaving the passing whole-archive
digest in production.

The next discriminating test should pin the *exact 542 archive bytes* as a
known vector in the no-stub SHA stream spec, compare one-shot and streamed
digests on the same retained array, and inspect the first differing block or
call boundary. Repeated-byte and synthetic mixed-byte vectors pass, but they
do not cover this archive content. After a correct bounded digest passes
admission, test an archive larger than one chunk and measure paired time/RSS.

## Follow-up: bounded byte feed passes three chunks (2026-09-29)

The descriptor array and an owned copy both had the correct one-shot archive
digest, yet `sha256_stream_v1_update` on the owned array returned the wrong
digest. Feeding scalar bytes through `sha256_stream_v1_update_byte` produced
the admitted digest. This isolates the failure to the native array-update
call path in this context; the root cause remains unproven.

The trial pinned descriptor digest read buffered windows of at most 65,536
bytes and feeds each byte to the bounded SHA state. A no-stub native spec
admits the original 542-byte archive and a 131 KiB archive that spans three
digest reads, verifies a member, and closes the capability: 9 examples,
0 failures, 0.18 s, 13,244 KiB peak RSS under a 2 GiB virtual-memory limit.
This is correctness and bounded-read evidence, not a paired performance
qualification. The per-byte call cost must be measured on realistic archive
sizes against the prior whole-archive path; if it fails the normalized
time/RSS rule or hard limits, replace it with a correct block update before
the change is promoted.

The isolated worktree does not contain `bin/simple` or native MCP/LSP server
wrappers. The available Stage-2 capsule supports `native-build` but rejects
the `-c` and `check` commands used by the core smoke and source-check scripts;
the MCP native smoke stops at its missing server binary. These broader gates
remain unverified pending a current-source self-hosted runtime and wrappers.

## Follow-up: paired 8 MiB performance rejection (2026-09-29)

A focused no-stub native entry opened and verified the same deterministic
8,388,608-byte CAS file using the prior reader (`9361eda0179`) and bounded
byte-feed reader (`f41c8838915`), compiled with the same Stage-2 capsule and
host runtime bundle. Each process ran under a 2 GiB address-space limit;
one warm run per binary preceded nine alternating paired samples on the same
host. Both returned `pass`. The baseline binary was 115 KB, the candidate
130 KB.

| Metric | Prior reader | Byte-feed candidate | Candidate / prior |
| --- | ---: | ---: | ---: |
| p95 elapsed | 0.55 s | 0.77 s | 1.40 |
| median elapsed | 0.52 s | 0.76 s | 1.46 |
| peak RSS | 76,760 KiB | 135,596 KiB | 1.77 |

The normalized p95 time plus peak RSS ratio is **3.17**, above the `<2`
gate, with gaps much larger than sample spread (baseline 0.51–0.55 s;
candidate 0.75–0.77 s). Per-byte Simple calls likely allocate in this native
path, but that mechanism is not proven. The candidate was reverted; the
131 KiB admission test remains as a whole-archive regression. Raw samples
are in `doc/09_report/compiler/target6_pinned_digest_8m_pair_2026-09-29.json`.
Next, find a correct chunk update that avoids per-byte calls, then
rerun this same paired workload before considering the bounded reader.
