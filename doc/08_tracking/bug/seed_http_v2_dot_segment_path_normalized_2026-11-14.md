# Seed `rt_http_request_v2` rewrites `..` path segments before sending

BugDB ID: `seed_http_v2_dot_segment_path_normalized_2026-11-14`
Priority: P2
Status: fixed

## Symptom

After `seed_http_v2_u8_array_body_rejected_2026-11-14` was fixed, case 1 of
`test/03_system/app/devhub/feature/minio_binary_put_spec.spl` still fails on
the Rust seed. The loopback checker
(`test/fixtures/devhub/native_minio_binary_put/verify_loopback.py`) receives
the exact 5 body octets with the right SHA-256, but on the wrong path:

```
request_attempts=[('/bucket/direct.bin', 5, '27041e6e...f0fb')]
```

The fixture uploads key `dir/../direct.bin`; the checker requires the request
target `/bucket/dir/../direct.bin` verbatim, because the SigV4 canonical
request is computed over that raw path.

## Root cause

`src/compiler_rust/compiler/src/interpreter_extern/network/mod.rs`
`rt_http_request_v2` hands the URL to `ureq`, which parses it with the WHATWG
`url` crate. That parser always removes dot segments (`.`/`..`, plain or
`%2e`-encoded), and ureq writes `url.path()` into the request line with no
override, so the wire path no longer matches the path the pure-Simple caller
signed. The C runtime twin (`rt_http_perform` in `src/runtime/runtime_native.c`)
already sends the caller's request target verbatim.

## Fix

When the caller's request target has a dot segment, the seed extern now sends
it over a plain-socket HTTP/1.1 exchange (`verbatim_http_exchange`) that writes
the target byte-exact (fragment dropped, query kept), mirroring the C twin:
Host (unless the caller set one), caller headers, Content-Length, and
`Connection: close`. Before I/O it refuses a target carrying a control or
space byte (the url crate silently drops CR/LF/tab, so this is the request-
splitting guard), and refuses URL credentials or a caller
`Transfer-Encoding`/`Connection` header, which ureq would have acted on.
Header replacement follows ureq's `set` (`x-*` headers accumulate). The response keeps the ureq lane's tuple shape and limits
(lowercased header names, 1024 headers / 1 MiB, 8 KiB reason, 64 MiB body,
chunked decoding, no redirects). ureq still validates scheme and host
(`request_url()`), and paths without dot segments keep the unchanged ureq path.

Residual gap: `https://` with a dot segment cannot be sent verbatim through
ureq, so it now fails closed with a typed error
(`dot-segment path cannot be sent verbatim over https`) instead of silently
sending a different, unsigned path.

## Evidence

- Red on the base: `http_v2_sends_dot_segment_path_verbatim`,
  `http_v2_sends_encoded_dot_segment_verbatim_without_fragment`,
  `http_v2_dot_segment_path_decodes_chunked_response` and
  `http_v2_https_dot_segment_fails_closed_before_io` failed (the https case
  reported `https://127.0.0.1:9/bucket/direct.bin`, showing the normalisation).
  Green after the fix, together with `http_v2_dot_segment_classification`,
  `http_v2_dot_segment_rejects_control_bytes_and_unsupported_headers_before_io`,
  `http_v2_dot_segment_header_semantics_interim_response_and_trailers` and
  the dot-free pin `http_v2_plain_path_and_query_unchanged`
  (`cargo test --release -p simple-compiler --lib http`: 13/13).
- `test/03_system/app/devhub/feature/minio_binary_put_spec.spl` on a seed
  rebuilt from the fixed tree (aarch64): 3/3 pass (was 2/3), using wrapper
  executables that `run` the three fixture/app entry points and
  `DEVHUB_PYTHON_BIN=/usr/bin/python3`.
- Regression: `test/01_unit/lib/io/http_sffi_import_scope_spec.spl` 1/1 and
  `test/01_unit/app/devhub/itf_api_spec.spl` 15/15 on the same seed.
