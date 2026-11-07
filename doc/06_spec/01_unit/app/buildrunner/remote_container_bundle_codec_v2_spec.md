# Container completion bundle structural transport V2

Status: **AWAITING_VERIFICATION** — source-authored specifications and manual.
No compiler, seed, tests, wire codec, provider, or container was executed. There
is no runtime PASS or coverage claim.

Source: `test/01_unit/app/buildrunner/remote_container_bundle_codec_v2_spec.spl`.
Implementation: `src/app/buildrunner/remote_container_bundle_codec_v2.spl`.

`SIMPLE_REMOTE_CONTAINER_BUNDLE_V2` frames raw blobs in this order: encoded build
result, encoded V2 container completion, canonical common container execution
evidence, canonical engine-selected-user receipt, retained workspace probe,
stdout, stderr, output count, then each relative path and output blob.
The codec reuses the bounded chunk kernel and explicitly replaces its local
reader with the reader returned by each blob decode, preserving value semantics.
Budgets are 4 MiB cumulative raw blob plus output path bytes, 16 MiB wire,
16 KiB raw chunks, and 4096 outputs. Binary logs and output bytes are preserved;
nested text requires valid UTF-8 and its owning canonical codec.

The common fixture calls `container_execution_evidence_v2` with internally
consistent synthetic runtime wait and exact-absence observations and their
canonical digests. These values are codec fixtures, not provider observations.
The user receipt correlates the exact execution runtime, scope, request, provider,
and a synthetic engine-selected-user observation at time 990, before absence
time 1000. It does not identify the workload's effective UID or Windows SID.
The probe contains a fixture task digest, 64-hex nonce, and `write-read-delete`
record. No access cycle was executed to produce this fixture text.
The completion deliberately carries a structurally valid all-zero signature;
these transport specs do not claim signature acceptance or execution authority.
Its execution digest uses the common measurements domain frame over canonical
execution, canonical user receipt, and retained probe bytes.

| Scenario | Intended assertion |
| --- | --- |
| Full round trip | Preserve canonical execution and user evidence, retained probe and successful probe output, native container id and absence query digest, arbitrary binary bytes, UTF-8 escaped path, result, and V2 completion. Exact re-encoding matches. |
| Chunk boundary | Reassemble a 16385-byte stdout in two chunks, continue through distinct stderr and output blobs, and retain exact bytes. |
| Empty blobs | Empty logs and downloaded inventory round trip while the result may still claim outputs; only later parent verification can admit them. |
| Failed result | Failed results retain user/probe fields and their framed execution digest while both result and downloaded output inventories remain empty. |
| Untrusted substitution | A well-framed changed stdout decodes as changed bytes while the completion's original log digest remains unchanged. |
| Frame integrity | Native V1 frame, missing newline, truncated blob, and trailing rows reject. |
| Raw canonical form | Leading-zero lengths, incorrect chunk counts/sizes, uppercase hex, and escaped hex reject through the shared kernel. |
| Output inventory | Unsafe and duplicate paths and more than 4096 outputs reject on encode and decode. |
| Bounds | Oversized wire or raw length rejects; individual oversized and combined log allocations reject before encoding; a within-limit stderr declaration rejects when preceding execution, user, probe, result, and completion bytes consumed its budget. |
| Nested integrity | Invalid result, native completion header, invalid common absence/user proof, non-UTF-8 execution/probe bytes, and old V2 frames lacking mandatory user/probe blobs reject after raw reassembly. |

The codec contains no PID, native compiler process payload, or tree-reap field.
Decoding does not authenticate signatures, provider provenance, execution,
absence, log/output/test measurements, replay state, or publication authority.
Those remain separate parent admission and runtime qualification gates.
