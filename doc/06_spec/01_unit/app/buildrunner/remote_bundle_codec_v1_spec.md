# Remote completion bundle wire V1

Status: **AWAITING_VERIFICATION** — source-authored manual. No compiler,
seed, tests, real remote execution or transfer ran for these assertions.

Source: `test/01_unit/app/buildrunner/remote_bundle_codec_v1_spec.spl`.
Implementation: `src/app/buildrunner/remote_bundle_codec_v1.spl`.

The codec transports `RemoteCompletionBundleV1` as canonical line wire intended
for an `.sdn` transport artifact. The frame is
`SIMPLE_REMOTE_COMPLETION_BUNDLE_V1`. Ordered result, completion, process,
stdout and stderr blobs precede the ordered output count and path/blob pairs.
Every blob carries its byte length and exact chunk count. Chunks contain at
most 16,384 bytes, encoded as lowercase hex, with full chunks except the last;
empty blobs have zero chunks. Text uses explicit UTF-8 conversion and is
decoded only after all its byte chunks have been assembled.

The aggregate decoded budget is 4 MiB including result/completion/process text,
logs, output bytes and output path UTF-8 bytes. Wire size is at most 16 MiB,
output count is at most 4,096, process text is at most 2,048 bytes, and the
frame admits at most 32,768 lines. Hex parsing bypasses the generic per-character
scalar unescaper; encoding collects bounded chunk parts and joins them.

| Scenario | Intended assertion |
| --- | --- |
| Binary and UTF-8 roundtrip | Zero, 128, 255 and newline bytes survive exactly; UTF-8 process text and a percent-bearing Unicode output path survive; result digest and completion signature remain unchanged; re-encoding is identical. |
| Chunk boundary | A 16,385-byte stdout blob has two chunks and roundtrips exactly. |
| Empty blobs | Empty process/log/output collections use zero chunks and remain empty. |
| Payload mutation | A correctly framed stdout mutation is preserved as changed bytes. Structural decoding does not authenticate evidence. |
| Framing | Unknown versions, missing terminator, truncated chunks and trailing rows reject. |
| Canonical fields | Leading-zero counts, count/length disagreement, short hex, uppercase hex and escaped hex reject. |
| Output paths | Unsafe/duplicate decoded paths and duplicate/unsafe encoded paths reject. |
| Bounds | Wire above 16 MiB, declared raw length above 4 MiB, output count above 4,096 and encoded raw evidence above the aggregate budget reject. Two individually bounded logs also reject when their combined bytes plus metadata exceed the budget. |
| UTF-8 | Invalid UTF-8 in reassembled process text rejects, while logs and output bodies remain encoding-neutral. |

Fixtures contain a signed completion plus structurally valid synthetic result
and evidence data. They do not claim that those bytes match the signed digests
or that a process ran. After decoding, the receiving parent must independently
freeze and compare its actual bytes, verify the original approval/grant and
protected host signature, check current fences/cancellation and durably consume
replay state before publishing. Decoder success grants none of that authority.

Execution and runtime performance remain unverified; no PASS or coverage claim.
