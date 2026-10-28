# SCV Draft Blob Store v1 — BDD Contract

Status: **NOT_RUN**. The fetched release worktree has no `bin/release` runtime,
so this executable SSpec has not produced runtime evidence. The scenarios are
written in `test/03_system/app/scv/feature/scv_gateway_draft_store_v1_spec.spl`.

## Contract

The owner stores native object bytes of at most 1 MiB beneath a host-created,
private store root. The API uses `[u8]` for request and readback values, so NUL
and non-UTF-8 bytes are preserved. The caller supplies an internal host-attested scope with
repository/principal identity and read/write capabilities. Request identity
fields bind to that scope; they are not authorization claims. This module checks
canonical/no-follow path identity but relies on the host to create the root as a
private 0700 directory beneath a host-owned private ancestor, then durably sync
the root and its ancestor entry before use. The owner cannot sync or inspect
ancestors above the supplied root.

A write persists a versioned SDN intent record, the SHA256-addressed immutable
blob, then a versioned SDN local receipt. Each publication uses a private
staging directory, file and directory fsync, no-replace publication, and
readback. A recovered intent can finish from the exact supplied request bytes;
intent alone never returns an acceptance receipt. Existing receipts and blobs
are re-synced and re-verified before replay acknowledgment. Reads check the
admitted read capability before path lookup and verify the stored SHA256.

Ordinary staging write, fsync, readback, and publication failures attempt to
remove the temporary stage. If path identity changes or cleanup fails, the
private stage may remain. The owner does not scan or recover old temporary
stages and does not promise retention cleanup.

The receipt state `local_durable` describes this local filesystem owner only.
This source does not implement gateway wire operations, network authentication,
remote acceptance, draft plans, chunk upload, Git publication, or production
durability qualification. Concurrent replacement by another OS principal is
excluded by the host-owned private root precondition; path APIs do not defend
against a hostile same-principal process replacing ancestors concurrently.

## Scenarios

| Scenario | Evidence asserted |
| --- | --- |
| Put/get | Exact digest, byte count, local receipt state, and readback |
| Identical replay | Same receipt after object verification |
| Reused request ID | Different payload is rejected without replacement |
| Read/write policy | Known digest denied without read; read-only scope cannot write |
| Identity binding | Request principal mismatch is rejected |
| Namespace isolation | Same request ID has independent per-principal storage |
| Input bounds | Digest mismatch, oversized blob, and symlink root are rejected |
| Damaged bytes | Get and accepted-request replay reject a corrupted object |
| Interrupted write | An intent without an object is not itself accepted; recovery verifies get and replay if it completes |

The executable spec exercises successful replay and interrupted-intent recovery.
Fsync failure injection is not exposed by the owner, so failure of replay
barriers is statically reviewed but not fault-injected here.
