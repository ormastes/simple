# Native C HTTP client accepted incomplete response framing

Status: fixed (PR #6049), verified by loopback matrix.

`rt_http_decode_chunked` / `rt_http_content_length` in
`src/runtime/runtime_native.c` (POSIX core-C client) accepted chunked bodies
missing the zero chunk or final CRLF, chunk sizes with suffix/sign/space/`0x`
prefix/overflow, and conflicting duplicate Content-Length. Distinct from the
Simple-language decoder bug `decode_chunked_malformed_size_silently_truncates_body_2026-08-06.md`.

Fix: checked hex accumulation; success requires zero chunk plus the empty line
ending the trailer; identical duplicate Content-Length accepted, conflicting
rejected; failure leaves status/body outputs unset.

Verification: `sh scripts/check/check-runtime-http-framing.shs --output DIR`
(POSIX; Docker `gcc:14` on Windows). 33 cases x write strides 1/7/4096 = 99
runs. Before fix: 63 pass / 36 fail. After: 99 pass / 0 fail. Repaired client
sha256 `1a2c4f9ec0ce4580b0cc337b7c89e3f6fdce66fe4686f6b1756c7f08ceff0303`
(reproduced by the .shs port).

Not covered: TLS, redirects, timeouts, full trailer/extension grammar,
Transfer-Encoding ordering, TE/Content-Length ambiguity. Windows core-C HTTP
stays unsupported. Self-hosted checks unrun (no admitted self-hosted runtime).
