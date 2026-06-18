# TLS Application-Data AEAD Smoke Interpreter Blocker

Date: 2026-06-17
Lane: pure Simple SSH/HTTPS servers
Status: Resolved in lane evidence

## Summary

The release smoke needs stronger HTTPS evidence for TLS application-data AEAD
handling. A deterministic helper was attempted in `src/lib/nogc_async_mut/io/tls.spl`
to exercise the same TLS 1.2 application-data nonce, AAD, AES-GCM, and record
framing path used by `AsyncTlsStream.write/read` without opening a socket.

Executing the smoke failed before evidence could print:

```text
error: semantic: function expects argument for parameter 'end', but none was provided
```

The first local issue was fixed by changing TLS hex digit construction to slice
the ASCII hex alphabet directly. A second local issue in
`src/lib/nogc_sync_mut/io/tls_common_hooks.spl` was fixed by replacing
`hex_str.char_at(i)` with explicit `hex_str.slice(pos, pos + 1)` calls in
`_tls_hex_to_bytes`.

The root hook path was verified separately in
`test/01_unit/lib/io/tls_common_hooks_aes_gcm_spec.spl`. The remaining failure
was specific to routing the smoke through a new helper inside `tls.spl`, so the
release smoke now uses the already-tested TLS AES-GCM hook directly with a
deterministic TLS 1.2 application-data nonce, AAD, record header, and
`parse_record_hex()` verification.

## Impact

- Existing release smoke proves HTTPS release preflight, release routing,
  native protocol bypass rejection, HTTP 200 response composition, TLS
  application-data AEAD encrypt/record-parse/decrypt evidence, HTTP request
  parsing/routing, and TLS record-version rejection.

## Required Follow-Up

1. Keep `tls_common_hooks_aes_gcm_spec.spl` green for hook-level AES-GCM
   evidence.
2. Keep `pure_simple_server_release_smoke_spec.spl` green for server-lane
   encrypted/decrypted application-data evidence.
