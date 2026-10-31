# Native empty `[u8]` carrier from the bounded file read is rejected by `rt_http_request_v2`

- Canonical ID: `native_empty_byte_array_carrier_rejected_2026_11_01`
- Status: open; an active source workaround is not a runtime/ABI fix.
- Owner: DevHub adapter (workaround) / core runtime C + JIT ABI owners (fix).
- Created: 2026-11-01.
- Source: `src/app/devhub/adapter_minio.spl` (`minio_put_bytes`).
- Regression: `test/fixtures/devhub/native_minio_binary_put/main.spl` (empty-file PUT).

## Symptom

Natively compiled (`core-c-bootstrap`) `minio_put_object` on a zero-byte file
fails before any wire I/O with transport error `invalid HTTP v2 argument`
(the `rt_http_request_v2` argument validation in `src/runtime/runtime_native.c`).
The same call under the seed interpreter (ureq transport) succeeds, and a
fresh `[]` literal body passes native validation — only the empty-array
carrier produced by `rt_file_read_regular_no_follow_bounded_bytes` (zero-byte
file, `rt_read_regular_no_follow_buffer` arm 100) is rejected by
`rt_core_as_array` + `RT_CORE_ARRAY_FLAG_BYTES` checking.

## Evidence

Loopback fixture, native `minio_put` artifact: `put_bytes` with a literal
`[]` body -> accepted; `put_bytes` with the value returned by
`file_read_regular_no_follow_bounded_bytes` on an empty file -> `invalid
HTTP v2 argument`, deterministic across runs. Non-empty carriers from the
same reader are accepted, so the defect is specific to the zero-length
carrier path.

## Workaround

`minio_put_bytes` normalizes any zero-length body to a fresh `[]` before the
extern call. This is adapter-local and does not fix other owners passing
empty read carriers across the same boundary.

## Removal condition

Retire only after a natively compiled probe can pass the empty-file read
carrier straight into `rt_http_request_v2` (and sibling byte-array externs)
without rejection, verified on the loopback fixture with the deployed
compiler; then drop the normalization in `minio_put_bytes`.
