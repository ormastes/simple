# Read-only native SCV gateway v1

Source is implemented for a bounded loopback development service. Compilation,
SSpec execution, live GitHub routes, cross-host behavior and operational
qualification are pending the admitted runtime. This guide grants no release or
publication authority.

`scv gateway serve --config config/examples/scv_gateway_v1.sdn
--development-loopback --reason "local read integration"` starts the callable
server owner. Supply these arguments on one command line. Update the example's
logical repository, GitHub owner/name and immutable numeric GitHub repository ID
together. The schema requires exactly its nine fields; duplicate/unknown fields,
non-native syntax, files above 8192 bytes and final-component symlinks fail.
Only literal `127.0.0.1` and ports 1024–65535 are admitted. No HTTP request can
select a URL, a GitHub host, credentials, a command or another repository.

The named `bearer_token_env` is resolved once at startup through the application
environment facade. Set it through the runtime's secret owner to a 32–256 byte
header-safe random token. Never commit the token. Rotation requires restart.
Gateway client authentication and the gateway's upstream GitHub identity are
separate: only the server runs the existing bounded `gh` provider, inheriting
runtime-owned `GH_TOKEN`/`GITHUB_TOKEN` or stored GitHub CLI credentials. Native
clients use the runtime HTTP owner and need no Git/GitHub CLI or GitHub token.

The callable native client is `scv gateway read --endpoint
http://127.0.0.1:8877/scv/v1 --repository source --method capabilities --id
read-1 --token-env SCV_GATEWAY_TOKEN --development-loopback`. Supply the
arguments on one line. Replace `capabilities` with `read_ref`, `read_commit` or
`read_blob` and supply `--selector` with an allowed ref or immutable OID. A
capabilities request refuses a selector. The client normally requires HTTPS;
`--tls-address` supplies the numeric IPv4 connection address while the endpoint
hostname remains the TLS identity. It is an address, not a certificate path.
Plain HTTP requires explicit development authorization and literal loopback.
The fixed timeout is 5000 ms. Request and endpoint validation precede secret
resolution; a successful command prints the validated canonical native response,
and native failures exit nonzero. Client TLS availability does not qualify the
server's TLS owner.

Production startup without `--development-loopback` fails with `tls_unavailable`.
The current `SimpleHttpServer` TLS owner cannot activate encrypted transport.
The development flag and a printable 1–256 byte audit reason permit plaintext
only on loopback. Production exposure requires a separately approved and
qualified external TLS/authentication boundary or a qualified native TLS owner;
this implementation does not qualify either boundary and rejects nonloopback
listeners even if the caller claims a TLS proxy exists. Bearer authentication
does not protect the plaintext loopback socket from a privileged local observer.

The endpoint is `POST /scv/v1`, with `Content-Type: application/sdn` and one
`Authorization: Bearer ...` header. Every request eligible for native dispatch,
including unknown endpoints and capabilities, crosses authentication before
protocol decoding. The shared HTTP owner can reject malformed framing or unsafe
paths before invoking the application handler.
Duplicate authorization/content-type headers and query strings are refused.
Requests bind `version`, `id`, `repository`, `method` and `ref_or_oid` exactly.
Methods are `capabilities`, `read_ref`, `read_commit` and `read_blob`; writes,
publication and settlement have no route. The exact configured logical
repository is checked on each request independently of the method. Responses
carry `publication: not_publication` and `Cache-Control: no-store`.

Limits are fixed before native request decoding: request line 256 bytes,
16 headers of at most 1024 bytes each, body 4096 bytes, 18 bounded header-read
iterations, four admitted connections, connection-close framing and 5000 ms
socket read/write operation timeouts. These socket timeouts are per operation,
not a five-second end-to-end deadline. The response wire cap is 2113536 bytes;
the native body cap is 2105344 bytes and the decoded payload cap is 1048576.
Each read performs at most three fixed upstream provider invocations with
5000 ms per process and 2097152-byte response bounds. The server-side `gh` owner
controls any internal HTTP redirect policy; three invocations do not prove
three wire-level HTTP hops. Redirect behavior remains unqualified. Oversize inputs fail before decode;
responses are whole bounded records rather than truncated success prefixes.

GitHub owner/name and immutable numeric repository identity are verified before
and after each fixed read. Unsupported numeric GitHub routes fail closed.
Returned callback records are independently validated before envelope creation,
including logical/numeric repository, selector, type-specific shape and bounds,
verification enum and actual Git SHA-1 blob digest. This validation is pure and
shared with the provider owner. SHA-1 Git object format is the only advertised
upstream format. Commit verification is explicitly only an OID-field match;
the service does not claim to reconstruct or cryptographically verify original
Git commit bytes or signatures. Ref values are bounded observations, not an
accepted-state proof.

Native response payloads are lowercase hex. Blob payloads preserve arbitrary
bytes. Ref payloads are canonical SDN `{ref, oid, verification}`; commit payloads
are canonical SDN `{oid, tree_oid, parents, verification}`. Capabilities describe
limits and these restricted claims. `payload_id: sha256:...` proves payload
integrity only, never authentication, Git commit identity, publication or
settlement. Imported forged successes are refused before generating a valid
SHA-256 envelope. Provider failures are reduced to fixed redacted native error
codes. Predecode HTTP failures use the full native schema with ID `unbound` and
HTTP non-success; clients must reject them before request correlation. HTTP
framing errors occur in the shared transport owner and are not native RPC
responses.

The authored tests and their manual are
`test/01_unit/app/scv/gateway_service_v1_spec.spl` and
`doc/06_spec/01_unit/app/scv/gateway_service_v1_spec.md`. Run them once only after
runtime admission, then qualify actual localhost HTTP and GitHub network reads.
Injected provider tests are not live-network, TLS or operational evidence.
