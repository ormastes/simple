# Local canonical paged settlement

Implementation design, 2026-10-03. Selected Authority A / Adapters A / Operating B /
Retention A requirements remain unchanged. This source lane implements the local
bare-Git coordinator path for authoritative paged state; it does not qualify
protected GitHub publication, performance, host portability or retention deletion.
All new native test sources remain UNEXECUTED pending an admitted runner.

## Trace and authority

- REQ-022/023: preserve original signed work, exact parent/tree/OID, signed
  settlement receipt and independently read local receipt-index contents through
  restart, stale-head reconciliation and historical replay.
- REQ-029: use the existing settlement-work SJ CAS for durable transitions; no
  process/network wait occurs while that root lease is held.
- REQ-030: Git contains canonical semantic manifest, high-water summary and typed
  record pages. Raw evidence remains outside this projection in evidence CAS.
- Paged retention prerequisite: actual canonical paged publication/readback is
  necessary but does not implement pending-work fencing or authorize deletion.

A local index observation remains `local-index-observed`, never protected
`Indexed`. Receipt structs, journal decoders, blob results and cached metadata
are data; they do not admit a patch or grant remote publication authority.

## Frozen projection

`SCVDB-PAGED-GIT-v1` consists of these exact regular-file paths:

| Path | Contents |
|---|---|
| `scv/paged/manifest` | Existing canonical `DbPagedManifest` text |
| `scv/paged/high-water` | `SCVDB-PAGED-HIGH-WATER-v1` canonical complete sorted marks |
| `scv/paged/buckets/<four lowercase hex>.scvp` | One exact raw canonical record page |

There is no hex transport, corpus-sized payload array, obsolete page inventory in
the current tree or text conversion of binary bytes. Git history retains older
page versions. Candidates start from an authenticated parent index and replace
affected bucket entries; unchanged blob OIDs are retained. Readback rejects
missing/extra paths, nonregular modes, incorrect parent/tree, malformed metadata,
bad page hashes and high-water summaries that omit retained/deleted kinds.

Blob IO uses existing text process results only for object type, decimal size,
OID and generated temporary filename. `git unpack-file` writes actual bytes in
owned scratch; a bounded nofollow reader checks the exact regular file. Size is
checked before unpack/read. Publication uses `hash-object --no-filters` over real
staged bytes. Environment/config guards and private scratch registration remain
mandatory; no raw process ABI or caller-owned `verified` boolean is added.

## Interfaces and ownership

Shared candidate infrastructure:

```simple
db_git_candidate_require_owned_scratch(scratch) -> Result<bool, text>
db_git_blob_read_owned(scratch, oid, max_bytes) -> Result<DbGitBlobRead, text>
db_git_blob_put_owned(scratch, bytes, max_bytes) -> Result<DbGitBlobRead, text>
db_git_candidate_finish_index(candidate, message, raw_commit, expected_oid)
    -> Result<DbGitPreparedCandidate, text>
```

The first function checks the actual existing private registry and marker; it
does not accept a caller ownership assertion. `DbGitBlobRead` carries `oid`,
`size` and actual `bytes`. Finishing an index requires an already registered
candidate's fetched parent/scope. It is internal infrastructure, not a producer
semantic facade.

Paged owner surfaces:

```simple
DbPagedGitProjection { manifest, high_water, projection_digest }
DbPagedSettlementJournal { receipt, manifest_wire, projection_digest, phase }
DbSettlementPagedLocalConfig { scratch_parent, authority, policy, bootstrap_receipt }

db_settlement_resume_paged_local(root, expected_queue_head, config, sign_receipt)
    -> Result<DbSettlementLocalResult, text>
db_settlement_paged_readback_local(root, parent, receipt, authority, policy)
    -> Result<DbPagedGitProjection, text>
```

The queue keeps exact candidate commit bytes in its existing `candidate_commit`
field. Queue wire v2 adds a paged journal alternative; exactly one reference or
paged journal is valid for prepared/awaiting/terminal work. V1 remains readable
and reference-only, with unchanged original patch encoding. Backend selection
binds the reducer/protocol/structural policy and cannot silently migrate a
reference snapshot. An explicit signed paged genesis is required.

The existing scheduler and reconcile/publish/index loop are shared. Only backend
preparation, readback and reconstruction vary. Preparation reauthenticates the
original patch and reserved-kind gate, reads the actual indexed canonical tip,
drives `db_paged_begin/advance` with bounded actual proofs, stages immutable pages,
and persists the signed receipt/journal before push. Changed structure triggers
replanning only after actual history proves the old candidate unpublished.
Credential changes are reauthorized independently of structural compatibility.

Prepared journals pin their complete immutable page closure. Checkpoint installs
continue blocking prepared/awaiting work, preserve original queue bytes and
require accepted terminal identities. No page garbage collection may remove
objects reachable from a retained queue generation. Checkpoint compatibility
must be implemented and tested before enabling this queue variant.

## Validation and limits

Cold/foreign roots use `db_paged_validate_import`, including global typed index
invariants. A bounded private in-process owner registry may retain roots it
actually validated or produced through full incremental admission. Its key binds
local object root, repository, namespace, epoch, protocol, index grammar,
structural policy and semantic root. Restart requires cold validation; no public
disk `validated=true` marker is trusted. Actual page bytes are always hashed on
use and current key/metadata authorization is checked per operation.

Limits: 65,536 bucket descriptors; 16 MiB per raw page; 16 GiB cold page bytes;
16 MiB manifest/inventory result; 1,024 high-water kinds; existing 64 MiB planning
proof budget and 10,000 operations. Queue limits remain 64 items/16 MiB encoded
state, so large retained descriptors can cause explicit backpressure. No quota
is a measured RSS or throughput result. Blob/candidate work is per affected page;
cold full validation remains explicit maintenance work.

The 16 GiB source cap is per pass: cold Git blob import, each of the two existing
global validation passes, recovery high-water scanning, and changed-page export
are separately bounded. They do not share an operation-wide 16 GiB IO allowance.
Global validation also retains its existing spill/conflict-cache quotas. Signed
receipt ancestry uses the existing 32-commit settlement history bound; older
unproved history fails explicitly rather than allocating or guessing. Local
object commands disable lazy fetch; explicit transport owners alone fetch.

### Process cost and invalidation

Cold Git import performs bounded inventory/metadata calls followed by several
Git processes per page: object format/type/size checks, `unpack-file`, and the
shared ownership/configuration checks. The importer then performs the existing
full local invariant validation. For B buckets this is O(B) process launches,
in addition to bounded local validation and spill IO. It is a correctness-first
maintenance path; no 10,000-record import latency or Operating B qualification
is established by this implementation.

Hot publication starts with `read-tree` of the authenticated captured parent.
Unchanged buckets retain their existing object IDs without blob readback or
rewriting. Each changed bucket currently requires blob creation and actual
readback plus an index update; removed buckets require an index removal. Git
index updates may be grouped only through a bounded safe input facility already
provided by the IO facade. An argv batch must not accumulate the whole corpus.
Manifest/high-water metadata and final tree/commit verification add bounded
fixed overhead. This source slice does not add a process ABI or claim batched
blob transport that the existing facade does not supply.

The private root cache expires on process restart and is bounded by entry count.
Its exact key changes with local object root, canonical context, structural
policy, protocol/index version or manifest root. Credential changes do not
invalidate structural validation, but current admission is always repeated.
Missing or changed local page bytes fail their actual hash check; a cache hit
never grants permission to skip page integrity or canonical Git readback.

## Acceptance source outline

Real local bare-Git fixtures must exercise two actors' alias allocation, original
signature/metadata refusal, exact OID after restart, publication-before-index
recovery, stale canonical HEAD without ID reuse, reverse-arrival dependencies,
credential revocation/rotation, historical accepted replay and original queue
byte preservation. Corrupted/missing/extra pages, wrong modes, forged marks,
wrong receipt/tree and reference-format migration must fail closed. Tests must
also cover reserved operation denial, checkpoint in-flight blocking and no
process wait under SJ. Blob tests independently cover binary NUL/non-UTF8 bytes,
size quotas, unowned scratch and malformed unpack filenames.

Core agent owns paged projection/readback/preparation, shared coordinator/queue
hooks, checkpoint compatibility and integration fixtures. Research agent owns
binary Git blob helpers and their tests. Root integrates; independent source
review is required before handoff. Protected provider capabilities, actual
runtime/crash receipts, Operating B timings/RSS and retention fencing remain
separate unfinished gates.
