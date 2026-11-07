# Historical Host exec child projection

The capacity owner replays a single distributed-operation journal. An exec
child is provenance for execution inside an already charged parent container;
it must neither debit a second reservation nor free its parent on completion.
Unknown actions still pass through the existing strict reservation validator.

`host_runtime_exec_child_projection_v3(journal, capacity, child)` returns only
`Result<bool, text>`. It creates no lease, delegation, grant, process or journal
event. All inputs are retained records, not trusted current authorization.

The exact child WAL envelope must match the canonical packet at
`host-runtime-exec-requests/sha256(child.id).sdn` (4 MiB bound). Shared V3
matchers validate the complete supplied controller/parent chain and intent
payload. The ordinary parent must independently exist in the same actual WAL;
its exact envelope and reservation payload must match that chain. The child
subject, project, environment and memory match the original charged parent.
Its requested provider control window cannot exceed its own operation duration.
The parent launch grant's old expiry does not limit a later child grant.

The original V2 execute packet, creation intent, and original execution
observation must agree on plan, full scope, native CID, provider generation,
runtime identity, baseline provider pin, operation/request digests and retained
grant identity. A latest inspection cache cannot replace the original record.
Missing, malformed, substituted or orphaned evidence rejects the entire reopen.
The supplied controller assignment is correlated structurally to Host-retained
evidence; this does not assert that Host stored its assignment object originally.

After successful validation only the child allocation row is omitted. Every
original parent reservation and its existing charge/release proof remain under
the capacity owner's ordinary projection. Child admitted, executing, unknown,
completed, failed and cancelled states confer no release authority. Reopen's
existing recovery transition still makes interrupted execution uncertain.

Dependencies point from capacity owner to this read-only module to common
contracts/journal and bounded evidence loaders. The module imports no capacity
owner, local root, command, provider, current clock or cryptographic authority
owner. No second WAL or token registry is introduced.

Integration ancestry: this worktree starts at
`51d1823fefea53d1a8a086ba2811ce1aa182dda9`, before PR #7743's improved parent
completion proof. The existing capacity-file delta is exactly one import and a
narrow validated-child branch. Root must apply that delta onto its current
proof-aware capacity owner and preserve the landed completion validator.
Shared packet dependency is immutable `071358d1635` (root aggregate `40abd`).

Status: source only. Authored real-WAL/reopen SSpec is **NOT_RUN**. Synthetic
native observations and valid fixture signature frames do not qualify current
authorization, native exec, owned native lifecycle or installed control policy.
