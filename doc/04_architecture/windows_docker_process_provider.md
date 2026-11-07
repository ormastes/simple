# Windows Docker process provider architecture

Status: source implementation; AWAITING_VERIFICATION, 2026-11-07.

The Windows leaf under `std.nogc_async_mut.container.providers.windows` is the
canonical first Windows bridge. It uses Docker over an explicitly selected local
named pipe and explicitly requests process isolation. This replaces the earlier
containerd/runhcs first-bridge proposal; the historical design is retained with
an amendment. The controller must introduce a versioned Windows dispatch variant;
its Linux request cannot be interpreted as Windows.

The policy holds the trusted engine endpoint and identity, provider generation,
boot identity, selected host/image versions, executable and finite I/O bounds.
The request holds workload identity, immutable image, command/arguments and hard
resource limits. A canonical digest binds request content; operation identity
remains separate. The provider copies common lifecycle envelopes to its owner.
Only exact full native IDs and matching inspected labels authorize lifecycle work.

A caller must persist the frozen request and intent before create, then retain the
returned native ID before continuing. The initial provider's in-memory state is
not a durable journal. Recovery requires that caller-owned exact identity and
checks the engine's current observations. Loss of the create response cannot be
resolved by scanning or adopting a user-chosen name. It remains blocked for
operator reconciliation; the provider never guesses, repeats an ambiguous create,
or performs broad cleanup.

Each operation rechecks engine identity before using its bound ID. Image and
container inspection bind digest, image identity and actual process isolation.
Unknown native errors preserve uncertainty. Scripted execution is an exact argv
fixture seam and cannot qualify the platform. Native command construction uses
the process facade, never a shell string.

The trusted controller is responsible for workload authorization and durable
commit. Broad pipe membership is not a per-client security policy. No arbitrary
mounts, Hyper-V, WSL or global pruning are admitted. Source-level policy checking
is not proof that Windows enforces CPU, memory or network limits.

No startup/latency/RSS claim exists: warm probe, create/start/wait, bounded logs,
stop/destroy and restart recovery measurements require an admitted compiled
Windows runner and live source-matched fixture. Repeated engine checks are
intentional identity invalidation checks; caching them across a mutation would
hide daemon replacement. Large inventories and full engine scans are forbidden.

## Shared Simple Container API and continuity

All orchestrator/host consumers route through `std.nogc_async_mut.container.api_v2`.
The Windows adapter owns typed policy/request projection and delegates Docker
commands to Windows leaves. Linux remains its own Podman leaf behind the same API.
The common scope separately carries native machine identity, physical-host alias,
service scope, provider generation, continuity mode/id and actual native boot ID.
The legacy RuntimeIdentity boot slot carries the canonical scope hash as an
internal fence only. Managed Docker labels retain actual `simple.boot` separately
from `simple.fence`, plus physical/service/incarnation/mode/native-machine labels.

Windows MachineGuid and architecture are native OS observations. The documented
successful-boot counter is typed lower-assurance data and cannot prove continuity
after restore/reset. Native CNG creates a service-incarnation nonce; copied text
is not live authority. The finite strong-boot factory refuses this weak route.
Host/orchestrator must supply the actual persistent owner, startup managed-scope
inventory quarantine and separately epoch-bound grants before Windows activation.
The inventory helper returns conservative quarantine candidates, including exited
and dead objects; failures or uncertainty never release capacity or adopt objects.

Create/start use the common grant-bound launch deadline after observations and the
shared admitted native capture owner at the spawn boundary. Expiry does not cap
workload lifetime or grant cleanup authority. Read/log/wait require no fabricated
fresh launch grant. Stop/destroy require retained explicitly authorized lifecycle
ownership. Independent absence uses a fresh successful empty exact-ID query, not
a destroyed cache phase; common evidence serializes the actual query/result.
