# SCV gateway compile-source snapshot replication v1

Date: 2026-10-27. Source implementation target after the authenticated draft
blob PUT/GET slice. This design is scoped to immutable compile-source snapshot
inventories. It does not claim a full SCV history replica, repository replica,
cross-host TLS qualification, Git publication, settlement, or validation
admission. The server entrypoint remains the existing explicit development
loopback service until TLS is separately qualified.

## Contract

The client submits the exact `SCV_COMPILE_SNAPSHOT` provenance and
`SCV_COMPILE_INVENTORY` bytes from a validated frozen compile snapshot. The
canonical manifest binds the repository and configured principal, domain
`compile-inventory-v1`, opaque effective-configuration digest, commit/tree/
revision IDs, inventory digest/count, and typed source object descriptors.
The configuration digest is identity input only; this protocol does not
receive or validate the configuration bytes.

The server reuses the draft service's authenticated bearer-to-grant mapping and
the grant's repository/principal-scoped object namespace. It recomputes the
inventory digest, exact row count, canonical path/order/uniqueness and
file-versus-directory conflicts, then recomputes tree, commit and revision IDs
using the existing `compile_snapshot_values_v1` owner. The source closure comes
from those verified inventory rows, not a caller-supplied completeness flag.
Only declared compile source files are in scope; this is not filesystem
absence, repository history, editor-event, generated-input, or configuration
completeness evidence.

Every source object must be present in the caller's scoped blob namespace,
have the exact declared byte count, and hash to its inventory content ID. A
missing object produces a bounded `needs_inputs` list and can be retried after
the client uploads that exact content. A present but malformed, non-regular,
corrupt, or hash-mismatched object is an integrity error, never `needs_inputs`.
Before root acknowledgment, every required blob is durably re-put/re-synced;
the immutable root record and receipt are then published with no-replace,
fsync, exact readback, and directory fsync. Identical retries return the same
receipt; a conflicting root ID or bytes refuse. The store has no deletion or
GC API, so the immutable root record acts as a logical pin under current
append-only storage, with no unpin/GC integration claim.

Optional structural recipes may be linked per source path. Each uses only the
exact `scv-byte-root-v1` and `scv-byte-node-v1` records, verifies legacy
`syntax_node_` IDs, traverses all child and payload references, and reconstructs
the original linked raw bytes and length exactly. Recipes are optional metadata
bound by the manifest, not proof that every source has a recipe. Unsupported
recipe schemas or any mismatch refuse publication. The compile-source closure
remains complete for its declared inventory whether recipes are present or not.

## Bounds and behavior

All protocol messages, missing-reference responses, source object sizes, total
snapshot bytes, row counts, and per-request transfer batches have explicit
limits. The client uploads only required missing inputs, in bounded batches,
with stable idempotency IDs. Partial transfers leave unpinned immutable blobs;
they do not create or replace a root. No operation deletes remote objects or
interprets omitted paths as deletion.

The existing draft client remains the transport owner, including endpoint
policy, pinned TLS for external clients, bounded framing, credentials callback,
and redaction. The existing service remains the auth owner. The snapshot
protocol adds typed methods to these seams and a durable root owner to the
existing draft store rather than a parallel token policy or generic database.

## Tests and evidence

Unit specs cover identity recomputation, canonical and empty inventories,
duplicate/path-prefix rows, malformed counts and IDs, repository/principal
pins, missing versus corrupt objects, typed structural child/payload closure,
wrong raw association, duplicate retry, conflicting root, and bounded
`needs_inputs`. The loopback system spec covers a real native HTTP exchange,
upload/retry/finalize, exact root receipt, read-only grant denial and recovery
from a partial transfer. Runtime qualification, cross-host transport,
performance, operational durability drills, and GC/unpin remain separate gates.
