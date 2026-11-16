# Shared orchestration server contexts

Status: source and documentation are under implementation. Examples describe
the planned CLI contract. Runtime, cross-host connectivity, native packaging,
LinuxPodman and WindowsDocker qualification are **NOT_RUN**. No example below
identifies a provisioned or reachable server.

Simple, Simple Orchestrator, Caret and agents can share a named server or select
separate servers through one strict SDN document. Server selection does not
enroll a host, authorize a workload, change a Caret listener or expose a
container runtime socket. See the [architecture](../../04_architecture/server_contexts.md)
and [host identity setup](orchestration_host_identity.md).

## Server document

Example `~/.config/simple/servers.sdn`:

```sdn
version: 1
currentContext: development
servers:
    local:
        transport: local
    build:
        transport: ssh
        host: build.example.test
        port: 22
        containerHost: host.docker.internal
        authRef: "secret://work/build-login"
        tlsRef: "trust://work/build-host-key"
        remoteExecutable: /opt/simple/bin/simple-orchestrator
    agent-build:
        transport: ssh
        host: 192.168.50.20
        port: 2222
        authRef: "secret://work/agent-login"
        tlsRef: "trust://work/agent-host-key"
        remoteExecutable: /opt/simple/bin/simple-orchestrator
contexts:
    development:
        sharedServer: build
        consumers:
            caret: local
            agent: agent-build
```

`sharedServer` is required and must name an existing server. `consumers` is
optional and accepts only `simple`, `orchestrator`, `caret`, and `agent`.
Here Simple and Orchestrator select `build`, Caret selects `local`, and agents
select `agent-build`. Every reference is checked, including unselected contexts.

Selection order is explicit server, selected context's consumer mapping, then
selected context's shared server. An explicit context selects the context;
otherwise `currentContext` does. An invalid explicit context fails even when
an explicit server was also supplied. Invalid files and missing explicit
references never become a local request.

Documents are limited to 64 KiB, sixteen servers, and sixteen contexts. The
strict parser rejects duplicate keys, unknown fields, wrong scalar types,
unsupported versions and malformed syntax. Names are bounded ASCII identifiers.
DNS labels and canonical dotted IPv4 are accepted. Integer, octal, hexadecimal
and shortened IPv4 spellings fail; IPv6 returns
`server-host-ipv6-unsupported` in this version. Address validation is lexical;
it does not query DNS or prove connectivity.

SSH requires a port in 1..65535, `secret://` authentication reference,
`trust://` host-key policy reference, and bounded absolute `remoteExecutable`
with safe path segments. Quote references because they contain colons. Keys,
passwords and tokens never belong in these fields. A local record omits all
address, credential, trust and executable fields; their defaults are empty and
port zero. HTTPS records are representable, but current consumer selection
returns `server-consumer-transport-unsupported`.

## Planned CLI

```text
simple-orchestrator server-resolve <config-file|-> <consumer> <context|-> <server|-> <host|container>
simple-orchestrator server-request <config-file|-> <consumer> <context|-> <server|-> <host|container> <profile-file> <request-file>
```

For the config argument, `-` requests default configuration discovery. For
context and server arguments, `-` selects the normal defaults. These are
argument sentinels, not stdin. `host` retains the configured host;
`container` requests container address selection explicitly.

```sh
simple-orchestrator server-resolve /home/alice/.config/simple/servers.sdn orchestrator - - host
simple-orchestrator server-resolve /home/alice/.config/simple/servers.sdn agent development build container
simple-orchestrator server-request /home/alice/.config/simple/servers.sdn orchestrator - build host /home/alice/.config/simple/build-ssh.sdn /home/alice/requests/inspect.sdn
```

These commands are intended usage examples; they have not been executed.
`server-resolve` selects configuration only. `server-request` uses the profile
appropriate to the selected transport. The HOST CONFIG `server_config`
key references the server document; it does not embed endpoint or identity
fields into machine build defaults. Discovery reads, in order:

1. An explicit config path supplied to the command.
2. `SIMPLE_SERVERS_CONFIG`.
3. `SIMPLE_SERVERS_SDN`, a bounded inline public snapshot.
4. User HOST CONFIG `server_config`, with the session override
   `SIMPLE_HOST_SERVER_CONFIG` taking precedence over the file value.
5. `~/.config/simple/servers.sdn`.

The user HOST CONFIG file is `~/.config/simple/host.sdn`, overridden by
`SIMPLE_HOST_CONFIG`. This first app-loader slice reads the user host file and
session override; it does not load machine defaults or legacy per-hostname
layers. Discovery reads configuration without changing the environment.

Only an absent implicit `~/.config/simple/servers.sdn` produces the local
default. A missing or unreadable explicitly selected file, environment-selected
file, or `server_config` target fails. An unreadable implicit file or malformed
selected document also fails. `-` requests discovery; it does not force local
operation when a remote configuration was selected by that discovery.

## Profiles and installed gateway policy

An SSH client profile binds the selected server's references to local files:

```sdn
kind: server-ssh-profile
version: 1
authRef: "secret://work/build-login"
trustRef: "trust://work/build-host-key"
user: buildsvc
sshExecutable: /usr/bin/ssh
identityPath: /home/alice/.ssh/build_orchestrator_ed25519
knownHostsPath: /home/alice/.ssh/orchestrator_known_hosts
hostKeyAlias: build-controller
```

These nine fields are required. Optional `sshDigest` and `storeRoot` default to
empty strings. `authRef` and `trustRef` must match the selected
record's `authRef` and `tlsRef`. Paths are absolute and use safe segments.
The profile, identity and known-hosts files must satisfy the loader's private
file policy. Parent directories must be trusted; separate no-follow checks
and OpenSSH's later file opens do not provide an anchored path-swap proof.
Follow [host identity setup](orchestration_host_identity.md) for provisioning
and verification of the actual key and independently trusted host-key entry.

For the Windows client, both optional fields are required: `sshDigest` is the
64-character lowercase SHA-256 of the local OpenSSH executable, and `storeRoot`
names the protected identity store. The executable uses an absolute drive
path, for example `C:/Windows/System32/OpenSSH/ssh.exe`; its lower owner pins
the actual image. Native private-store namespace spelling is preserved.
Relative paths and traversing segments are rejected. The remote executable
remains the remote server's absolute executable path.

The current Windows store deliberately returns
`identity-store-transport-projection-unavailable` after validating the actual
protected root or target. External OpenSSH cannot yet consume a proven stable
key path. Windows SSH therefore fails closed, and `key-profile-install` rejects
this capability before publication. A functioning counted-stdin process owner
does not remove this separate path-projection blocker. Local key and pin
publication can still return their logical references and public fingerprints;
see the setup guide for exact receipts.

When `storeRoot` is present on either host, `identityPath` and `knownHostsPath`
must exactly match validated existing store paths for SHA-256(`authRef`) +
`.key` and SHA-256(`trustRef`) + `.hosts`. The client validates the public pin
against `hostKeyAlias`; private key contents stay in the store and OpenSSH.
The same store owner remains held through child execution and all cleanup.
POSIX clients may retain the legacy private-file configuration above. The
platform command owner and store owner both remain attached to an error reply
when cleanup cannot be confirmed. These source paths require admitted native
verification; this change does not claim a completed Windows execution test.
On Windows, install the profile as a distinct protected-store record named
`<64 lowercase hexadecimal digits>.profile` under `root/journal/`. Its contents
remain SDN; `.key` and `.hosts` records cannot be loaded as profiles. The
loader opens and reads the actual ACL-protected store, then closes its owner
before permitting the decoded executable configuration to take effect. A
failed close returns its retained owner and rejects the configuration. POSIX
continues to accept its private regular profile file. Native private-root
namespace spelling is retained for protected opens; external SSH paths must
come from the store's validated path API, without unchecked prefix rewriting.
Synchronous transport polls yield a ten-millisecond scheduling quantum
while a healthy Windows command is unfinished, preserving the SSH handshake
budget without reconnecting or resubmitting the operation.

SSH uses explicit identity and known-hosts paths, strict host-key checking,
noninteractive authentication and disabled forwarding. It invokes only the
configured compiled executable and fixed `gateway-stdio-v1` command. Request
fields travel in framed stdin, not a remote shell command.

For a local request, `<profile-file>` is the trusted installed controller
gateway profile:

```sdn
version: 1
stateRoot: /var/lib/simple/orchestrator/controller
controllerId: work-controller
allowedActions: [submit, inspect, cancel]
```

The gateway profile is a private regular file with an absolute state root;
the state root must have mode 0700. On the SSH peer the fixed gateway reads
`SIMPLE_ORCHESTRATOR_GATEWAY_CONFIG`, or
`~/.config/simple/orchestrator-gateway.sdn` when that variable is unset.
This is trusted installation policy on the peer. A request cannot choose the
peer's state root or broaden `allowedActions`. A remote client supplies its
SSH profile, while the remote account supplies its own gateway profile.

## Request document and ownership

Every request contains all eight fields, including empty unused fields:

```sdn
version: 1
action: inspect
controllerId: work-controller
requestUid: request-20261115-001
source: ""
namespace: ""
name: ""
sourceDigest: ""
```

The requested controller identity must match installed policy and the action
must appear in `allowedActions`.

| Action | Required operation data |
|---|---|
| `submit` | Nonempty resource `source` text, valid `namespace` and `name`; empty `sourceDigest`. |
| `inspect` | Empty `source`, `namespace`, `name` and `sourceDigest`. |
| `cancel` | Expected source digest in `sourceDigest`; other operation data empty. |
| `dispatch` | Signed dispatch packet text in `source`; other operation data empty. |
| `resume-execution` | Signed execution packet text in `source`; other operation data empty. |
| `inspect-execution` | Empty operation data. |

Submit, inspect and cancel reuse the controller journal owners. Submission
records intent; cancellation records desired cancellation. Neither response
alone proves task execution or termination. Dispatch, execution resume and
execution inspection retain their existing signed host authorization and
execution owners. Gateway framing correlates a reply with a request; it does
not replace those authorization checks.

A transport failure after a mutation can leave the outcome uncertain. Retain
the request UID and reconcile through the controller. Do not automatically
retry a mutation with a new UID. The SSH owner must retain and collect its
process lease; unresolved cleanup is not success. Request and reply buffers
are bounded. The portable peer stdin reader is blocking, so an external
session supervisor is still needed for an elapsed-time bound on ingestion.

## Prepare an unsigned container plan

The application command projects configured public server discovery into the
native request before the request and plan digests are computed:

```text
simple orchestrator container-plan-prepare <linux-podman|windows-docker-process> <candidate-context.sdn> <native-request.sdn> <config|-> <consumer> <context|-> <server|->
```

The candidate context contains a versioned backend, canonical host scope and
provider policy. These are unverified input snapshots, not installed authority.
The native request uses the selected provider's existing retained-record codec.
The command emits the complete unsigned execution request and digests with
`signingRequired: true`, `admissionRequired: true`, `ownerVerified: false` and
`executionAuthorized: false`. It does not launch a container or contact a server.

An application composition path that obtains reservations, assembles the
required proofs, signs, submits and dispatches this candidate remains open.
Existing assignment, reservation and dispatch validators remain authoritative;
this preparation command does not create grants or rewrite signed packets.
All preparation specifications and backend fixtures are **NOT_RUN**.

## Container clients and outstanding evidence

In `container` mode the resolver chooses `containerHost` when present;
otherwise it keeps a nonlocal configured host. Local transport, localhost
aliases, the `.localhost` suffix, IPv4 loopback and unspecified destinations fail.
It never invents a host alias. The example `host.docker.internal` is an
explicit deployment choice; its presence and routing must be verified in the
actual container backend. Public endpoint configuration does not authorize
credential injection. Never mount the user's private host keystore, home,
SSH private key or a runtime socket into an agent container. Use a separately
approved scoped credential or host proxy when authentication is required.

The inline `SIMPLE_SERVERS_SDN` snapshot is consumed after an explicit config
path or `SIMPLE_SERVERS_CONFIG`, and before host-file/default discovery.
`SIMPLE_SERVER_CLIENT_SCOPE=container` forces container address validation even
when an ordinary CLI call passes `host`. These public launch values do not
attest placement or authorize effects. They are included before request signing
and provider digest calculation, never inserted into an already signed plan.
The launch projection also includes `SIMPLE_SERVERS_CONFIG=""` to clear an
inherited image path that could otherwise shadow the signed public snapshot.
All three entries are covered by the native request/plan digest.

## Implementation and evidence matrix

| Surface | Source status | Runtime evidence |
| --- | --- | --- |
| `simple orchestrator server-*` | Linked command route | NOT_RUN |
| Standalone `simple-orchestrator server-*` | Shared config and SSH controller route | NOT_RUN |
| Caret `orchestrator server-*`, consumer `caret` | Shared route and existing reply validators | NOT_RUN |
| `agent` consumer context | Strict selection and container address projection | NOT_RUN |
| Linux SSH client | Owned framed stdin/capture, strict host keys | NOT_RUN |
| Windows SSH client | Owned stdin adapter; protected external key-path projection unavailable | Fail closed; NOT_RUN |
| Container API launch projection | Immutable public env, provider network policy required; application signing/dispatch producer remains open | NOT_RUN |
| Host key generation/pinning | Retained private-store generation, pinning and protected profile installer | NOT_RUN; OpenSSH interoperability unverified |

The fixed remote command expects a compiled standalone `simple-orchestrator`.
Its installed profile allowlist gates metadata and signed execution attempts.
The SSH process budget is 120 seconds for dispatch/resume and 30 seconds for
other requests. Successful framing still requires controller/request identity,
source-digest and nested execution validation. It does not prove completion.

The [test plan](../../03_plan/sys_test/server_contexts.md) lists the outstanding
runtime gates. The [contract manual](../../06_spec/01_unit/lib/common/config_core/server_context_v1_spec.md)
is manually authored and records **NOT_RUN**. No warm-start latency, request
latency, RSS, remote mutation, or LinuxPodman/WindowsDocker receipt is claimed.
