# Historical semantic and evidence resolution

Implementation slice for REQ-032 (honest resolution), REQ-019 (exact historical
configuration/reproduction dependency evidence), and REQ-030 (controlled evidence
placement). This supports evidence lookup for REQ-019, not a new reproduction
executor or a claim that every configuration dependency is available. No runtime or remote
authority qualification is implied. This owner performs no network IO.

## Trust chain and representation

Capture an independently expected active generation, follow its checkpoint
anchor, and authenticate that actual checkpoint with `DbCheckpointAuthority`.
The requested revision must occur in the signed history catalog and be reachable
from its current root. A catalog entry is not evidence that historical bytes
still exist. Reference `History.object_digest` is SHA256 of the exact snapshot
wire; Paged history binds the manifest revision. Neither is a controlled-CAS
digest: CAS addresses hash the domain-separated content/dependency envelope.

A locator is an untrusted hint from signed semantic object digest to CAS digest.
Every use reopens the CAS object, verifies its envelope digest, decodes the exact
semantic wire, and checks both the requested revision and signed object digest.
A fallback walks actual retained parent generations with bounded reads. A
retained object address, public struct, or caller boolean grants no authority.

The historical row supplies the bundle digest. The caller supplies only a
revision and typed manifest entity. Reuse the existing `run_manifest` entity and
`DbCiDurableManifest`; do not add a competing evidence-manifest identity.

## Immutable producer projection

`DbCiManifestDraft` contains `provider_instance`, `project`, `run_id`,
`manifest: DbEvidenceRevision`, and `bundle_digest`.
`db_ci_manifest_operations(draft)` returns one `AppendObservation` operation.
Its exact Text fields are `version = scv-ci-manifest-v1`, `provider_instance`,
`project`, `run_id`, `manifest_revision`, and `bundle_digest`. The entity kind is
`run_manifest`. Existing independently reviewed schema/metadata and key policy
must permit these fields; the owner never signs or manufactures an allowlist.

The original authenticated patch goes through the existing Reference or Paged
apply owner. `db_ci_manifest_from_row(row, accepted)` checks the exact projection
and derives `DbCiDurableManifest.accepted_batch_digest` from `row.revision` and
actual accepted-registry membership. Embedding that digest in the creating
patch would be circular, so it is not a field. Older rows without this exact
projection produce `HistoricalProjectionUnavailable`.

## Interfaces

- `db_store_read_generation(root, channel, head) -> DbStoreView` is an additive
  read-only local-store entry. It reuses the existing no-follow generation
  decoder/hash checks and does not change HEAD, journals, or queue schemas.
- `DbHistoricalRequest { revision: text, manifest: EntityRef }`.
- `DbHistoricalAuthority { checkpoint: DbCheckpointAuthority,
  expected_active_head: text, expected_retention_head: text }`.
- `DbHistoricalSources { evidence_parent: text }`.
- `DbHistoricalLimits { max_history_nodes, max_generation_hops,
  max_semantic_bytes, max_evidence_bytes, max_total_read_bytes,
  max_rollup_hops }`, all unsigned counts/bytes, bounded as below.
- `db_history_archive_current(root, channel, expected_head, config,
  paged_policy?, sources, limits) -> Result<DbArchivedSemantic, text>` captures
  actual current state and publishes/readbacks its semantic wire in CAS with
  an empty dependency list. The receipt records backend, semantic revision,
  signed-object-format digest, CAS digest, captured generation, and observed
  byte count. It is an observation, not a signed checkpoint or import receipt.
- `db_history_query(root, request, authority, sources, limits)
  -> Result<DbHistoricalResult, text>` captures authority, resolves history and
  actual semantic bytes, obtains the historical row/acceptance proof, and
  verifies the selected evidence object.

`DbHistoricalResult` pairs provenance with a typed resolution:

- `Exact(DbEvidenceFileInfo)`: streaming digest/EOF verification of the actual
  selected object, including its dependency names; no raw-content allocation.
- `Aggregated(DbRetainedRollup, raw_unavailability)`: actual rollup CAS bytes,
  replayed provenance, and exact coverage of the historical raw digest.
- `Restricted(DbEvidenceFileInfo)`: actual digest-verified ciphertext/retained
  classification; no plaintext or key handling.
- `Unavailable(reason)`: typed unknown/outside-history, absent/corrupt semantic
  bytes, missing projection, missing historical identity, absent/corrupt evidence,
  IO failure, quota, or rollup-provenance failure. Scope and authentication
  failures remain errors rather than benign missing data.

Provenance records requested revision, captured active generation, checkpoint
digest, history object digest, semantic CAS hint actually verified, retained
generation when used, requested/resolved manifest entity, manifest revision,
accepted batch digest, selected evidence digest, retention generation, optional
rollup digest, and observed content bytes. Missing proofs use optionals.
`Exact` describes the selected object; dependency names are not a claim that
every transitive object was hydrated or durably pinned.

## Historical identity and Paged behavior

Paged settled aliases resolve against the requested historical manifest using
actual alias, row, accepted-batch and actor-counter page proofs. No current
alias/index may substitute for a missing historical page. These are selected
record inclusion proofs, not a fresh global imported-index validation claim.

Reference provisional UIDs match actual historical snapshot rows. A settled
alias may use the checkpoint's signed identity map only when the requested
revision equals that checkpoint's own revision. Older Reference history does
not bind identity maps; return `HistoricalIdentityUnavailable` instead of using
current mappings. Tombstoned or absent manifests do not resurrect evidence.

Paged archive publishes the manifest image, not an invented external page
closure. Actual immutable `page_store` objects remain the page source and must
be reopened and verified for each required proof. Missing pages are unavailable.

## Resource and effect boundaries

Use one explicitly threaded budget/cache per query. Cap history traversal at
4096 nodes, retained-generation traversal at 64, semantic images at 16 MiB,
selected evidence objects at the existing 1 GiB ceiling, rollup chains at 64,
and total reserved reads at 8 GiB (default 4 GiB). Per-read bounds are clamped
or reserved before IO; unsuccessful attempted reads also consume a reservation.
Page cache retains at most 64 MiB of encoded-page reservations. These limits
are not measured CPU, RSS, or throughput qualifications.

Evidence resolution uses the existing streaming retained-handle inspector and
its digest/EOF/metadata checks. A 100 MiB selected object must work without a
100 MiB byte array. Semantic codecs and small rollups remain separately bounded.
Locator publication uses a scoped trusted parent, no-follow, private staging,
no-replace, fsync, and readback. A failed locator publish may leave harmless
verified CAS bytes; it never publishes semantic acceptance or mutates HEAD.

Retention fallback is explicitly pinned local adapter provenance. Its verified
rollup content/coverage does not prove canonical-remote retention authority or
protected settlement. Historical key/schema availability, older Reference alias
archives, external Paged page archives, and remote authority admission remain
separate gaps. This slice does not implement epoch/backend migration.

## Regression source plan

1. Admit two real immutable manifest patches with different bundles; archive
   the first state, advance HEAD, and query the genuinely older signed revision.
2. Reject a locator pointing at another valid CAS semantic image; missing and
   corrupt historical images remain distinct from missing raw evidence.
3. Reopen actual old parent generations when no archive locator exists; verify
   hashes/context and bound the walk without changing any HEAD.
4. Exercise exact, replay-verified aggregate, actual restricted ciphertext, and
   missing evidence against the historical row-derived digest.
5. Resolve a Paged settled alias from the old manifest after current state
   advances; fail on its missing historical page. Reject unsupported older
   Reference aliases while permitting the current signed identity map.
6. Stream a real 100 MiB fixture in fixed chunks; assert content size/digest and
   unchanged semantic/retention/checkpoint heads, plus small quota failure.
7. Cover unsigned/wrong checkpoint pin, projection/default-deny admission,
   entity/namespace mismatch, accepted/counter mismatch, linked paths, loops,
   malformed locators, and exact reservation boundaries.
