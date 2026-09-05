# SimpleOS HTTP worker split visibility gap

Status: statically repaired; executable proof remains blocked

The worker monolith was split below 800 lines into `worker_owner.spl`,
`worker_connection_extensions.spl`, `worker_wire.spl`, and a narrow
`worker.spl` facade. The strict module boundary was repaired in the same wave:

- `Worker`, its construction/abort surface, `resource_snapshot`, and the
  snapshot fields are explicitly public through the facade;
- cross-file worker methods, `OP_*`, `TlsSessionState`, and wire helpers are
  package-visible and named in minimal explicit export lists; and
- `worker_wire.spl` explicitly imports `TlsSessionKeys` from the canonical TLS
  common owner, whose complete existing cross-file TLS API is now explicitly
  exported.

The split preserves one mutable `Worker` owner and keeps wire helpers out of the
public facade. Each TLS receive stream is installed once in the Worker's map;
each receive removes that value before ingest, then reinserts the sole mutable
owner only after framing and authentication commit. This respects the
language's indexed-access value semantics without leaving the map's 32 KiB
fixed ring live during mutation, so one-byte fragmentation cannot induce a
copy-on-write clone per receive. The focused behavioral case feeds a maximum
legal record through that remove/mutate/reinsert path and checks committed
identity, empty retained state, and linear byte work.

The SimpleOS `WebService` now publishes the started server owner
before later lifecycle transitions, and rollback/stop/cancel reclaim a snapshot
of the lifecycle's currently active worker IDs. A partially successful cleanup
therefore remains retryable instead of trying to complete an already-completed
numeric prefix forever. Behavioral coverage constructs a two-worker lifecycle,
pre-completes one worker, and proves public cancellation reclaims the remaining
owner and reaches `Cancelled` without reading source text.

Static import/export, file-size, whitespace, and placeholder scans pass.
Executable compilation and server evidence remain unavailable because no
admitted self-hosted runtime exists; this record closes only the exact source
visibility and retryable-owner defects.

No runtime result is claimed; the admitted self-hosted runtime remains absent.
