# Shared orchestration server contexts

Status: implementation in progress; runtime verification unavailable. This is
not a deployment receipt or evidence of a reachable server.

The selected user requirement is shared or separate IP/domain orchestration
servers for Simple, Simple Orchestrator, Caret and agents, configured in SDN,
including container clients. Kubernetes kubeconfig supplies the reference
pattern: named endpoints, named contexts and explicit selection. Kubernetes
Service DNS illustrates discoverable container addresses. Neither Kubernetes
nor YAML is a dependency of this design.

## Ownership and interfaces

`std.common.config_core.server_context_*_v1` owns strict decoding and pure
selection. `ServerRecordV1` carries transport, host, port, optional explicit
container host, credential/trust references and a compiled remote executable.
`ServerContextV1` maps the four consumers to named server records and supplies
a shared fallback. `ServerConfigV1` selects the current context.

Selection first validates the explicit context (or current context), then uses
an explicit server, the selected context's consumer override, or its shared
server, in that order. Invalid explicit configuration never falls back to
local. An absent default file preserves local operation. Configuration is
bounded to 64 KiB and sixteen records/contexts; duplicate/unknown keys and
dangling references fail. V1 supports DNS and strict dotted IPv4; IPv6 is
explicitly unsupported rather than weakly parsed.

Machine HOST CONFIG remains the source of machine defaults; orchestration
`HostConfigV1` remains enrollment intent. Server contexts do not attest a host,
enroll an agent, authorize a workload or replace either schema.

## Transport and domain boundary

SSH is the first remote transport. The client uses strict host-key checking,
explicit identity and known-hosts paths, no agent forwarding, no implicit SSH
configuration, and one validated compiled executable with the fixed
`gateway-stdio-v1` command. Task fields travel in bounded framed stdin and
never enter a shell command. Credentials remain in local credential files;
SDN carries references and paths, never key/token contents. HTTPS records are
configuration intent only until a consumer has an admitted transport; requests
must fail explicitly, never fall back to HTTP or local execution.

The remote account's installed gateway profile chooses controller identity,
state root and allowed operations. The request supplies only typed operation
data and a stable UID. Submit/inspect/cancel reuse the existing controller
journal; submit retains intent, cancel records desired cancellation, and
neither claims observed execution or termination. Signed dispatch must retain
the existing controller/host authorization boundary. A generic host gateway
frame is not a controller command and must not be substituted for one.

`std.nogc_sync_mut.io.stdin_command_v1` supplies one opaque process owner to
the application. Its selected POSIX adapter retains `OwnedProcessLease`; its
Windows adapter retains the counted-stdin Windows command owner. Applications
contain no platform process branches. Windows requires a protected identity
store and a lowercase SHA-256 executable digest. A retained store validates
the exact private/public leaf paths bound to selected credential references;
only the public pin is read into application memory. The store remains live
until child cleanup finishes, including validation and launch failures.
Windows profile loading itself uses the store's separate `.profile` role,
not key/pin contents: a retained ACL-protected read produces a load turn and
failed-close owner. Only confirmed profile cleanup permits the strict SDN
parser's result to authorize execution. Native private-root namespace spelling
is preserved for capability opens; public paths use the validated store API.

The process owner retains its SSH lease through bounded polls and collection.
Transport uncertainty never retries a mutation; the caller reconciles the same
UID. Unknown/rejected cleanup cannot be reported as success. Stdio counts are
bounded, but the existing portable stdin reader is blocking; remote request
ingestion needs the SSH/session supervisor for an elapsed-time bound.

The synchronous IO facade uses a ten-millisecond scheduling quantum. POSIX
poll already waits within that bound. On Windows, one healthy unfinished
facade poll adds a ten-millisecond scheduling wait around the lower zero-wait
step, yielding CPU and preserving the finite caller's SSH handshake budget.
Cancellation, completion and failure cleanup add no wait. This scheduling
policy never reconnects or resubmits a request; the Windows cooperative owner
itself stays nonblocking and enforces the actual monotonic process deadline.
Both process and protected-store owners remain attached to failed replies
when their cleanup is unresolved. A consumed close error still blocks success.

## Container discovery

Container clients use an explicitly advertised container-reachable host or a
non-loopback configured host. A host loopback address never silently becomes
`host.containers.internal` or `host.docker.internal`. The Simple Container API
owns backend selection for LinuxPodman and WindowsDockerProcess; discovery
metadata does not open the runtime socket, launch a process, attest DNS or
prove connectivity. Credentials are mounted through separately authorized
container policy. Actual network mapping must be supplied and verified before
claiming deployment.

## Cost and qualification

Decode once per CLI invocation; resolve over at most sixteen records. No
recursive scans, DNS probes or retry sleeps in request selection. Each request
uses one SSH process and bounded frame buffers. Admission targets are <=64 KiB
configuration, <=2 MiB requests, <=8 MiB replies, <=120 seconds command budget,
and no unbounded retained output. Startup, latency and RSS must be measured on
the admitted self-hosted executable; no measurements exist for this change.

No runtime is admitted in this session. Authored specs, static review and
source landing remain AWAITING_VERIFICATION; they do not complete the broader
orchestrator or establish cross-host success.
