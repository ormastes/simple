# itf minio_get_object decoded lossily and reported character length

Status: verification-pending
Date: 2026-11-16

`src/app/itf/adapter_minio.spl` (separate copy of the DevHub adapter) fetched
object bodies via `rt_http_request` (text body, no truncation/UTF-8 check) and
reported `content_length: body.len()` (characters; 6 for a 9-byte body). Binary
objects came back as corrupted text.

Fix: ported DevHub's `_minio_get_checked` (v2 raw bytes, Content-Length truncation
check, strict `validated_utf8_bytes_to_text_linear`, fail closed) and use
`byte_len()` for content_length and PUT length/threshold.

Spec: `test/03_system/app/itf/feature/itf_minio_get_decode_spec.spl` (RED 6 vs 9 and
binary accepted; GREEN 2/2). `adapter_minio_spec.spl` 17/17.

Not covered: itf GET retry (itf has no retry module); the itf copy is still a
duplicate of the DevHub adapter (unification left to owner).
