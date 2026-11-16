# devhub minio: text body length counted in characters, not bytes

Status: verification-pending
Date: 2026-11-16

## Defect
`src/app/devhub/adapter_minio.spl` used `body.len()` (character count) where a
byte count is required:
- `minio_put_text`: size-limit check, signed `content-length`, and the
  `Content-Length:` wire header. A multibyte body (`"café ☃"`: 6 chars, 9 bytes)
  was sent with a short Content-Length, so the server saw a truncated body and the
  x-amz-content-sha256 did not match (`not the SHA-256 of the body`).
- `minio_get_object`: `GetObjectResult.content_length` reported characters.

## Fix
Use `byte_len()` in those four places.

## Specs
- Reproducer: `devhub_minio_emulated_spec.spl` "puts multibyte text with a
  Content-Length that counts bytes" and "reports the byte length of a multibyte
  object body" (fixture `test/fixtures/devhub/emulated/s3/object_multibyte.txt`).
- Generalization: the GET spec also asserts the decoded body round-trips; the PUT
  spec asserts the server-side body equals the sent text byte-for-byte.

## Not covered
`src/lib/nogc_sync_mut/io/external_text_io.spl` audited: no defects found.
`minio_get_object` still decodes via lossy `bytes_to_text`; not changed here.
