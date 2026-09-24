# KPF Tooling Daemon Document-Session Protocol

The tooling daemon exposes a transport-neutral protocol facade over the existing
`tooling_kernel` workspace. It does not implement or duplicate language analysis.

## Protocol negotiation

- Version `1.0` is accepted.
- Unknown major versions and newer unsupported minor versions fail before a
  connection slot is allocated.

## Document revisions

- Opening a document creates a language session pinned to one provider generation.
- Updates must strictly increase the immutable document revision.
- Analysis requests must name the exact current revision and content digest.
- Publishing a newer snapshot cancels all older in-flight requests for the document.

## Cancellation and disconnect

- Explicit cancellation is idempotent.
- Cancelled requests cannot publish diagnostics.
- Disconnect closes all document and language sessions owned by the connection,
  releases their generation pins, and rejects later requests through stale handles.

## Acceptance scenarios

The executable specification verifies protocol negotiation, stale update and
request rejection, superseding-update cancellation, explicit cancellation,
current-result publication, and connection teardown.
