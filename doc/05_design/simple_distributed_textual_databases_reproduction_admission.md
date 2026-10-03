# REQ019 configuration and reproduction admission

This source checkpoint extends existing signed transaction owners. Runtime execution,
full REQ019 completion, Operating B scale and the 36 selected requirements/15 NFRs
are not qualified by this checkpoint.

## Canonical records and admission

`db_reproduction_codec` reuses `DbConfigRevision`, `DbReproductionRevision`,
`DbObservation` and exact `DbEvidenceRevision` references. Immutable append-only
rows of kinds `config`, `reproduction`, `observation` contain exactly `version`,
`revision`, `canonical_record`. Version v1 is strict: malformed, noncanonical,
legacy shape-only records, duplicate dependencies and unknown versions reject.
The content revision hashes domain-separated canonical typed fields excluding
only the record's own revision, including its exact identity and all semantic
fields. Claimed revisions are recomputed; metadata review covers the full record.
Original signed patch bytes are never rewritten or resealed during admission.

Pure structural checks run in Reference admitted planners and Paged proof-based
transactions. Generic producer facades return `SCVDB_OBSERVATION_OWNER_REQUIRED`;
the dedicated `db_observation_apply_reference` and `db_observation_apply_paged`
owners authenticate current policy, capture the actual generation, resolve exact
records, verify content and delegate existing semantic CAS. Accepted replay still
reauthenticates the patch but does not claim current content availability.

Paged dependencies resolve through captured alias/row proofs. Comparison-only
normalization preserves signed alias-bearing records and their content revisions.
Reference `DbLocalImage` has no authoritative identity map: exact UID dependencies
work, but settled-alias dependencies fail closed. Adding authoritative Reference
identity capture remains an implementation gap; no row/counter-derived map is
invented. Its negative source oracle documents this limitation.

## Actual content and durable protection

`DbObservationSources.evidence_parent` is an external caller-owned absolute root.
The owner verifies effective-values, invocation and observation payload objects,
and declared dependency digests/statuses against actual bounded CAS observations.
Actual envelope edges must be declared. Available requires verified bytes;
restricted requires actual encrypted content or trusted retained classification;
missing requires authoritative absence; expired requires retained deletion
provenance. Corrupt, unreadable, scope-invalid and quota failures reject, rather
than becoming unavailable. Truthfully unavailable dependencies may accompany a
custom failure. No reproduction command is executed.

Verified available roots are pinned through the existing retention catalog before
final content recheck and semantic CAS. A losing CAS leaves permanent protection.
Actual missing/restricted transitive edges use the same catalog's distinct
`reproduction_incomplete` permanent marker after a bounded graph recheck under
its actual SJ writer. This is protection intent, not complete closure evidence.
The strict planner refuses every collection and prepared deletion resume while
such a marker exists, including a restricted child already cataloged. Ordinary
pin setters cannot remove reproduction pins/markers; marker expiry must be zero.
There is no trusted repair/release owner in this checkpoint. Restoring bytes alone
does not clear the marker: whole-catalog collection remains paused indefinitely
until a future trusted repair transition is implemented.

`DbObservationClosure.all_declared_available` describes the inspected declared
artifacts only. Full source/test artifact mapping under their respective digest
domains is not implemented; exact signed source/test references alone are not
content proof. The API makes no `reproducible` claim. Generic CI bundle closure
remains distinct from semantic reproduction admission; no automatic CI producer
mapping to these records is implemented here.

## Settlement and producer routes

The existing queue retains unchanged signed wires. Both local settlement resume
APIs accept optional final `observation_sources`; ordinary patches retain their
old defaults. Evidence patches need configured sources before preparation and
again after uncertain-outcome reconciliation proves unpublished, before candidate
publication. Already accepted work follows authenticated replay semantics.
Paged candidate prepare/restore are trusted application primitives; the actual
in-tree caller is the content-checking queue coordinator, not a producer facade.
They are not independently exposed as content-admission authority.

Integration-owned CLI routes `observation-apply` and `paged-observation-apply`
provide independently pinned policy, bounded patch and evidence parent to these
owners. CLI source/tests land separately; this lane does not edit commands.

## Implemented bounds and remaining target

Typed patch projection allows 64 records, 1 MiB encoded record and bounded lists.
`DbObservationLimits` currently caps 256 dependency nodes and 8 MiB materialized
objects because the existing pin/register owner has those limits. Its default
1 GiB `max_total_read_bytes` is an artifact-read reservation ceiling, not total
operation IO: repeated catalog/HEAD reads are separately bounded by legacy owners.
The incomplete graph owner separately caps 256 nodes and 32 MiB aggregate reads.
Paged proof/query caches retain their own cumulative budgets and bounded rounds.

The selected 100 MiB object / 1 GiB closure capability and Operating B target remain
open: streaming/paged retention pin integration is required. These interim limits
do not redefine the target, and large-object acceptance is not claimed.

## Source evidence

`db_reproduction_codec_spec.spl` covers canonical roundtrip, wrong content revision,
truncation, trailing bytes and duplicate dependency rejection. Actual filesystem
Reference/Paged cases in `scv_db_observation_it_spec.spl` cover signed admission,
truthful unavailable closure, corruption, replay, stale/forged writes, generic
bypass, permanent protection, prepared-deletion refusal, Paged alias comparison
and explicit Reference alias rejection. `scv_db_observation_settlement_it_spec.spl`
uses local bare Git, signed bootstrap/index, queue reopen and unpublished-candidate
content recheck. Helpers use `setup_item2_observation_*` / `check_item2_observation_*`.
All Simple source tests are UNEXECUTED; no admitted runtime or coverage result is
available. This checkpoint is implementation evidence, not verification completion.
