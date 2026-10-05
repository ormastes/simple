# HTTPS bodies were UTF-8-decoded on read: every image/wasm body corrupted (2026-10-05)

Status: FIXED (branch `work/tls-binary-read`)

## Symptom

No image fetched over https ever rendered in the Simple browser (google.com
logo, wikipedia.org globe). The image request was serviced (status 200,
`Content-Type: image/png`, `Content-Length: 2478` for the google logo) and
then rejected by `_store_image_response` with `image load error: invalid PNG
signature`. The canonical hex body started `efbfbd504e47...` (U+FFFD, then
"PNG") instead of `89504e47...`.

## Root cause

`h1_client.read_tls_response_bytes` read TLS with `conn.read_text_timeout`
and converted each chunk back with `text_to_bytes`. Under the interpreter,
the text extern's wrapper
(`src/compiler_rust/compiler/src/interpreter_extern/net_tls_client.rs`,
`text_from_runtime_parts`) builds the result with `String::from_utf8_lossy`,
so every byte sequence that is not valid UTF-8 became EF BF BD. The runtime
itself returned the raw bytes intact (`net_tls.rs`). Affected:

- every binary body over https (PNG, wasm, gzip, fonts);
- text bodies too, whenever a multi-byte UTF-8 character straddled the
  8192-byte read boundary (silent mojibake).

Plain http was not affected: `read_tcp_response_bytes` already used the byte
extern `rt_io_tcp_read`.

## Fix

A binary-safe read, `rt_tls_client_read_bytes_timeout_checked(conn,
max_bytes, timeout_ms) -> [u8]?` (nil = failure/timeout, empty array = clean
EOF, same contract as the text `_checked` read), on every lane:

- Rust runtime (`net_tls.rs`): the socket read now lives in one
  `tls_client_read_bytes_timeout` core that both the text and the byte
  externs wrap, so their behaviour is identical by construction.
- Interpreter (`interpreter_extern/net_tls_client.rs`): calls that core and
  returns an array of byte integers (as `rt_io_tcp_read` does); no text step.
- C OpenSSL runtime (`runtime_https_openssl_core.c`): `simple_tls_read` split
  into `simple_tls_read_core` (count / EOF / failure) used by the unchanged
  text read and the new byte read; the no-OpenSSL fallback returns nil.
- SimpleOS shim (`src/os/kernel/net/tls_shim.spl`): fails closed (nil).
- Simple side: declared in `tls_sffi.spl`, `browser_tls_read_bytes_timeout`
  (`browser_net_runtime.spl`), `TlsConnection.read_bytes_timeout`
  (`net/tls.spl`), and `read_tls_response_bytes` now uses it. Every existing
  text read API is kept.

### Lane parity (observed, not assumed)

| case | Rust | C (OpenSSL) |
|---|---|---|
| `max_bytes <= 0` / `timeout_ms <= 0` / unknown handle | nil | nil |
| clamps | 65536 bytes, 5000 ms | 65536 bytes, 5000 ms |
| clean close_notify | empty array | empty array (`SSL_ERROR_ZERO_RETURN`) |
| timeout / I/O error | nil; connection removed from the table | nil; connection marked broken |

Both lanes make every later read on a failed handle fail. The legacy C text
read still returns empty text for both failure and EOF (unchanged).

## Evidence

- Probe page with only the google logo `<img>`: hex body now starts
  `89504e470d0a1a0a`; the image reaches the PNG decoder (which then rejects
  its color type -- next gap, below).
- C loopback self-check (`scripts/check/check-runtime-https-openssl.shs`,
  new `binary` mode): a server writes all 256 byte values then
  close_notify; the client reads them through the byte API in <=100-byte
  chunks, gets them back unmodified, then an empty array (EOF); zero
  `max_bytes`/`timeout` and a closed handle read as nil.
- cargo: runtime `bytes_read_fails_closed_exactly_like_the_text_read`;
  interpreter `byte_read_result_is_lossless_for_every_byte_value` (0x00-0xFF)
  and `byte_read_keeps_nil_failure_distinct_from_eof`.
- Audit `scripts/audit/tls-client-sffi-fail-closed.shs` now requires the
  byte read on all four lanes (inventory 19 -> 20).

## Out of scope (named)

- `rt_tls_server_read_checked` has the same text-only shape, but it is
  Rust-only and not registered in the interpreter; a wss/https server that
  receives binary would need a byte variant too.
- Images still do not paint: `png_decode.spl` accepts only 8-bit RGB/RGBA,
  and both the google logo and the wikipedia globe are other PNG color types
  ("PNG bit depth or color type is unsupported").
