# Seed `rt_http_request_v2` rewrites `..` path segments before sending

BugDB ID: `seed_http_v2_dot_segment_path_normalized_2026-11-14`
Priority: P2
Status: open

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

## Root cause (by inspection, not yet fixed)

`src/compiler_rust/compiler/src/interpreter_extern/network/mod.rs`
`rt_http_request_v2` hands the URL to `ureq`, which parses it with the WHATWG
`url` crate. That parser always removes dot segments, so the wire path no
longer matches the path the pure-Simple caller signed. The self-hosted
runtime must send the request target unmodified for SigV4 to verify.

## Fix direction

Send the caller's request target verbatim (e.g. write the request line over
a socket, or a transport that does not normalise the path) in the seed's
`rt_http_request_v2`. Needs a red test that observes the raw request line.
