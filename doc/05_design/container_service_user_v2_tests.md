# Pure service and selected-user contract verification

Status: **NOT_RUN**. Source-authored tests only; runtime/platform admission remains separate.

The eight modern SSpec cases in `container_service_user_v2_spec.spl` use actual
`container_service_inventory_digest_v2`, `container_service_admission_valid_v2`,
selected-user encode/decode/digest and canonical runtime query digest functions.
No adapter, fake provider or callable host response replaces a production consumer.
The manual mirrors the eight exact `step` titles.

Inventory tests bind both the new owner scope and every old row. Old service epochs
on the same authorized alias/native machine/service are deliberately admitted for
quarantine reconciliation, while duplicate native identities or operation IDs,
invalid scope, uncharged rows and unsupported routes fail. Changing the new epoch
changes the hash. Alias and native machine retain distinct meanings. Empty arrays
require a successful complete native inventory outside this pure boundary.

ACK tests cover process-crash-v1 only, zero journal revision with empty commit digest,
and positive revision with an actual-format digest. Valid shape is not proof that
an actual journal commit exists; only trusted host ownership can supply that fact.

Selected-user receipts bind canonical query argv boundaries, backend, full runtime
identity, opaque scope fence, request/provider/query/evidence digests and observed
user bytes. Tests cover both backend shapes, strict wire and UTF-8 limits. Valid
shape cannot verify supplied hashes against an actual native query, or establish
effective workload UID/privilege. Such evidence must be produced and correlated by
the actual platform owner. A changed user changes the canonical receipt digest.

Read-only service factory review: refresh and quarantine-completion paths return the
updated tagged owner on success and failure. Start performs validation after adapter
creation and can return outer Err. Astra reviewed the actual Windows path: native
capture/inventory finishes before provider construction, startup remains quarantined,
and no workload, stream or host writer is acquired. Windows owner review confirmed
that provider.new and bind only construct data and retain no native handle or
writer. The factory now documents this narrow invariant; acquiring resources in
the future requires an owner-bearing start result. This is not a blanket exemption
for ownership-bearing constructors or a claim of native execution qualification.
No production source was changed by this test task.
