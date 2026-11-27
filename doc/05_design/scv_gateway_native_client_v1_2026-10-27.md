# Native read-only gateway client and bounded HTTP transport

Date: 2026-10-27. Source implementation and authored specs; execution deferred
until the parent admits Phase 3. Base `8dcbbbf949c`, owner
`/root/impl_tldr_route`, isolated branch `work/scv-gh-client-20261027`.
This implements the client part of the existing SCV gateway plan, not gateway
publication, protected-ref acceptance, commit-object proof or operational TLS
qualification. It consumes the frozen native protocol `f1626f5e01c`.

## Caller and policy

`app.scv.gateway_client_v1.scv_gateway_client_call_v1(config, request, credentials)`
uses `ScvGatewayClientConfigV1(endpoint, repository, allow_loopback_http,
timeout_ms, tls_address)`. `repository` is an independent policy pin, not a
value copied from an untrusted request. The endpoint must name `/scv/v1`.
The command/service owner wires this API into `scv gateway read`; it owns CLI
argument parsing and runtime environment access.

Credentials arrive through a trusted runtime owner callback
`fn() -> Result<text, text>`. The client calls it exactly once, after endpoint,
timeout and protocol request preflight. Tokens must be 1–4096 printable ASCII
bytes with no whitespace/control bytes. They enter only the Authorization
header; config and native SDN contain no credential. Provider, transport and
decode errors are redacted to stable codes, with no raw response, token,
request or upstream stderr logging.

Native methods are `capabilities`, `read_ref`, `read_commit` and `read_blob`.
The shared codec validates version, request ID, repository, method, exact
ref/OID selector, response kind/status, payload SHA-256 and the literal
`not_publication` claim. The client independently hashes Git's `blob <size>\0`
header plus decoded raw bytes against a requested blob OID (SHA-1 for 40 hex
digits, SHA-256 for 64). A sender-chosen valid payload SHA cannot replace that
check. Ref and commit metadata remain subject/field matched; they do not prove
a canonical commit hash, a protected branch update, or repository authorization
independently of the authenticated service policy.

## Endpoint and real transport boundary

HTTPS requires a separately pinned, canonical numeric IPv4 `tls_address`.
The canonical ASCII endpoint hostname is passed separately as TLS server name
through the existing TLS owner, preserving certificate trust and name checks.
There is no DNS lookup or automatic plaintext fallback. HTTP is allowed only
for literal `127.0.0.1`, with explicit `allow_loopback_http=true`. This supports
the service's explicit development-loopback mode; external TLS termination
uses the HTTPS client boundary. Userinfo, query/fragment, noncanonical ports,
control bytes, ambiguous path segments and alternate loopback host spellings
are refused. IPv6 and automatic DNS resolution are explicitly unsupported.

The shared `std.nogc_sync_mut.http_client.bounded_transport_v1` performs actual
TCP/TLS I/O through existing owners. It declares no externs and invokes no
Git, gh, subprocess or foreign HTTP command. TCP uses `TcpStream` timeout and
bounded byte APIs. TLS uses the existing `browser_net_runtime` address/SNI,
byte-read and timeout facades; those names denote a shared hosted network
owner, not a browser process. Handles close after either exchange outcome.

A positive timeout (at most 60 seconds) creates one monotonic network deadline.
Every connect/read/write receives only the remaining time. Partial writes must
make positive progress; each read requests at most 8192 bytes and the remaining
framing allowance. Header scanning advances once over received bytes. There
is no full-response unbounded convenience call.

## Framing and bounds

Responses require HTTP/1.1 status 200, exactly one Content-Length,
Content-Type `application/sdn`, and Connection `close`. Duplicate headers,
chunked transfer, Content-Encoding, Location, redirects and bare line breaks
refuse. Decimal length accumulation checks the configured limit before each
multiply/add. Header bytes are limited to 16384; response body bytes to the
protocol's 2105344. The generic transport has an additional hard 3 MiB body
ceiling. A single extra sentinel byte detects trailing/pipelined data, and
EOF is required after the exact declared body; truncation or timeout is not a
successful prefix. UTF-8 and SDN decode happen after those checks.

These are received-wire and owner read-allocation bounds, not a measured RSS
ceiling. Arrays may use word storage, and header/body/UTF-8/hash decoding makes
bounded copies. The prior generic native HTTP request path's 64 MiB transport
ceiling is not used or misreported as the smaller protocol bound.

## Authored evidence and remaining gates

`test/01_unit/lib/http_client/bounded_transport_v1_spec.spl` covers strict URL
policy, pinned address/name separation, length overflow/duplicates, hostile
framing, fragmented headers, truncation, trailing bytes and read allowances.
`test/01_unit/app/scv/gateway_client_v1_spec.spl` covers repository preflight,
credential acquisition count/redaction, the independently known empty Git blob
OID, response request-ID mismatch, and malicious bytes carrying a valid
sender-chosen payload SHA.

No checker, build, test, live network operation or docgen was run in this lane.
The parent must integrate the protocol first, then the client and service CLI.
Phase 3 verification must execute these specs, loopback requests through the
actual service/CLI, TLS certificate/name/pin failure cases, read-limit and
deadline failures, and realistic latency/RSS measurements. Source review is
not runtime admission, a native smoke pass, or cross-host qualification.
