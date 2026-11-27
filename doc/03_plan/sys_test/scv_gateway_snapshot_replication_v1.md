# SCV gateway compile-source snapshot replication v1 test plan

Executable specifications:

- `test/01_unit/lib/scv/gateway_snapshot_replication_v1_spec.spl`
- `test/01_unit/app/scv/gateway_snapshot_replication_v1_spec.spl`
- `test/03_system/app/scv/feature/scv_gateway_snapshot_replication_v1_spec.spl`

The protocol unit spec recomputes snapshot identity from exact provenance and
inventory bytes. It rejects wrong root IDs, malformed numbers, duplicate or
noncanonical paths, path-prefix collisions, repository/principal mismatch,
unbound objects, and unsupported recipes. An explicitly empty inventory is
valid only with its exact empty digest and zero count.

The store/service specs distinguish genuinely absent objects from present
corrupt, nonregular, or unreadable entries; confirm that incomplete roots
return bounded `needs_inputs`; reject structural child/payload omissions and
recipes that do not reconstruct the linked raw bytes; retry only after exact
blobs are uploaded; and ensure same-root retries are idempotent while changed
root bytes conflict. They also check principal-scoped authorization, bounded
missing batches, no delete behavior, and durable root readback.

The system spec drives the existing loopback native HTTP server and bounded
client through begin, needs-inputs, blob upload, and finalize. It checks the
exact durable receipt, retries after a simulated incomplete upload, and checks
read-only and cross-principal denial. No Git, BuildRunner, branch, ref, merge,
settlement, or publication side effect is exercised.

Execute each focused unit/system spec once with the admitted self-hosted
runtime. Runtime and docgen are **NOT_RUN** until that runtime is available;
the Rust bootstrap seed is not an acceptable substitute. Source inspection and
`git diff --check` do not establish behavior or durability qualification.
