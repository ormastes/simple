# Seed `rt_http_request_v2` rejects a pure-Simple `[u8]` body

BugDB ID: `seed_http_v2_u8_array_body_rejected_2026-11-14`
Priority: P2
Status: fixed (seed interpreter extern)

## Symptom

`test/03_system/app/devhub/feature/minio_binary_put_spec.spl` case 1 on the
Rust seed (`run` of `test/fixtures/devhub/native_minio_binary_put/main.spl`):

```
PASS native binary canonical typed SHA256
native binary direct accepted=false detail=rt_http_request_v2: body must be bytes
loopback native_exit=-6 request_attempts=[] verified_requests=[]
```

## Root cause

`src/lib/nogc_sync_mut/io/http_client_core.spl` declares the ABI as
`body: [u8]`. A `[u8]` literal such as `val bytes: [u8] = [0, 128, 255, 65, 10]`
reaches the seed's interpreter extern (`rt_http_request_v2` is spliced to the
interpreter under `run`) as a boxed element array (`Value::Array` of
`Int`/`UInt`), not packed `Value::ByteArray`. The extern
(`src/compiler_rust/compiler/src/interpreter_extern/network/mod.rs`) read the
body with `Value::byte_array_view`, which accepts only packed storage, so every
non-packed `[u8]` was refused before any I/O.

## Fix

Read the body with `Value::try_array_bytes`, the existing helper the other
byte-taking externs use (tls13, pbkdf2, signatures, io_file): it accepts packed
storage or boxed `Int`/`UInt` elements in `0..=255` and still fails closed on
any other element (out-of-range, negative, non-integer) with the same typed
`body must be bytes` error before I/O.

## Evidence

- Red: `http_v2_accepts_boxed_u8_array_body` failed on the base
  (`body must be bytes`); green after the fix. Negative test
  `http_v2_rejects_out_of_range_array_body_before_io` covers 256, -1 and text
  elements.
- Fixture: on a seed built from the fixed tree the loopback checker now
  receives the request with the exact 5 octets and SHA-256
  (`27041e6e...f0fb`), where before it received no request at all. The spec
  case still fails for a separate reason: the seed transport rewrites the
  `dir/../direct.bin` path (`seed_http_v2_dot_segment_path_normalized_2026-11-14`).
  The other two spec cases pass on that seed (2/3).
