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
