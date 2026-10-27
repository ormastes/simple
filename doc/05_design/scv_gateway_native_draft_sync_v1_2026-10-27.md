# SCV native draft blob sync v1

Date: 2026-10-27. This is a bounded native transfer path into the existing
private SCV draft blob store. It adds no GitHub API, Git operation, branch/ref
update, merge, publication, CI, or settlement capability.

## Trust and configuration

The service config is strict SDN with exactly these top-level fields:

```sdn
version: 1
listen_host: 127.0.0.1
listen_port: 8811
store_root: /var/lib/scv/draft-store
grants:
  - repository: repo-alpha
    principal_id: alice
    bearer_token_env: SCV_DRAFT_ALICE_TOKEN
    can_read: true
    can_write: true
```

The file is read without following its final symlink and is limited to 32 KiB.
Unknown and duplicate grant mappings are refused. Token values are resolved
from named host environment variables at startup, validated, and required to
map to exactly one configured repository/principal grant. Token bytes never
enter SDN or responses. A request cannot select a principal. The service
authenticates its bearer before decoding a request subject or deriving any
store path, then requires the request repository to equal the host grant.
Every store call receives a fresh capability value made only from that grant.

The operator must provision `store_root` beneath a private host-owned parent,
with private permissions and durable sync of the root and each naming ancestor
before starting the service. The service does not create or repair that root.
The store retains responsibility for canonical no-follow paths, exact request
replay, object digest verification, file and directory sync, durable receipt
readback, and recovery. The portable process cannot verify host ownership of
all ancestors.

## Wire and durability

Clients send one canonical `application/sdn` POST to `/scv/draft/v1`. A request
has version, wire id, repository, method (`put` or `get`), request id, SHA-256
content digest, and base64 payload. The principal is deliberately absent.
Base64 must round-trip canonically; raw blobs are capped at 1 MiB. The SDN
request and response cap is 1,405,000 bytes; the additive transport API also
has a 2,105,344-byte hard request ceiling while the pre-existing gateway client
keeps its 4,096-byte default.

A successful PUT response binds the configured principal, exact request
subject, digest and byte count to the storage owner's `local_durable` receipt.
An identical retry returns that receipt after the store re-verifies the
object. Reusing a request id with different bytes is rejected. A successful
GET returns the exact raw bytes and `local_readback`; it is not a PUT receipt.
All errors are stable codes and do not include token, filesystem path, or store
diagnostics. The client checks the response principal against its independent
host-selected principal pin.

## Runtime boundary

`scv gateway draft serve` runs only with explicit `--development-loopback` and
an operator reason. The native server has no qualified TLS listener and binds
only `127.0.0.1`; production startup fails closed. The native client may use
the existing pinned TLS transport when an external TLS endpoint is available.
The HTTP parser bounds bytes and per-read timeouts, but it has no wall-clock
deadline for a peer that continuously trickles a large body. Loopback-only
development is therefore the only admitted service mode pending bounded
server-body deadline support and TLS qualification.

## CLI

```text
scv gateway draft serve --config draft-gateway.sdn --development-loopback --reason "local integration"
scv gateway draft put --endpoint http://127.0.0.1:8811/scv/draft/v1 --repository repo-alpha --principal alice --request-id draft-7 --token-env SCV_DRAFT_ALICE_TOKEN --file ./draft.bin --development-loopback
scv gateway draft get --endpoint http://127.0.0.1:8811/scv/draft/v1 --repository repo-alpha --principal alice --request-id read-7 --token-env SCV_DRAFT_ALICE_TOKEN --digest <sha256> --output /tmp/received.bin --development-loopback
```

GET output paths must be absolute, use a canonical existing non-root parent,
and name a destination that does not exist. The client stages and verifies
bytes beside that destination, then publishes without replacement.

CLI `local_durable` means the server's private draft store returned its durable
receipt. It does not mean a Git object exists, a GitHub service accepted bytes,
a ref moved, checks passed, or settlement completed.
