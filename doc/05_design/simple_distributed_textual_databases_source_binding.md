# REQ019 explicit source/test mapping proposal

Status: interface frozen; application implementation written, source tests and independent review pending.
This adds the selected design's missing mapping to existing admission owners.

## Types and wire compatibility

Add DbSourceSnapshotRevision(reference:DbEvidenceRevision,snapshot_digest:text).
Reuse DbTestDefinitionRevision(reference,definition_digest). Add record variants
SourceSnapshot(value), TestDefinition(value), and BoundReproduction(value:
DbReproductionRevision,source:DbEvidenceRevision). Kinds are source_snapshot,
test_definition, and reproduction respectively. Existing Config/Reproduction/
Observation variants retain exactly v1 wire, revision domains and projection.
Only new variants use strict SCVDB-REPRODUCTION-RECORD-v2 and a v2 content domain.
Decoders reject version/tag mismatches, unknown fields and trailing bytes.

Source and test mapping revision hashes bind their exact immutable identity and
CAS ObjectRef, excluding only their own revision. BoundReproduction binds the
complete existing reproduction model plus exact source reference. Its
source.revision must equal value.source_revision. Observation.source_revision
continues to match that semantic revision; it is never interpreted as a CAS
address. Actual CAS envelope digests are snapshot_digest/definition_digest.
No mutable source label or caller-provided artifact-verified boolean is admitted.

## Actual owner transition

Extend pure record validation/lookup to source_snapshot and test_definition.
New custom FAIL admission must resolve exact config, bound reproduction, source
mapping and test definition from incoming records or captured rows. The original
signed records remain unchanged; aliases normalize only comparison values using
actual captured proofs. Reference alias limitation remains explicit.

Extend db_observation_expand and the existing Paged NeedKeys loop to obtain the
same closure; thread the current proof/query budgets without resetting. Source
and test CAS objects enter the existing actual inspector/register/pin/final-recheck
protocol. Existing Reference/Paged commands and local settlement coordinator
therefore use the same effect path, including unpublished-candidate recheck.
Generic guards reserve the two new owned kinds; immutable append-only rules,
full metadata review and accepted/counter replay remain mandatory.

Proposed failure codes: SCVDB_REPRODUCTION_MAPPING_REQUIRED for new custom FAIL using
legacy reproduction; SCVDB_REPRODUCTION_SOURCE_BINDING for differing semantic source;
existing REPRODUCTION_REFERENCE_MISSING/REVISION for exact lookup failures and
existing observation claim/corruption/scope/quota errors for artifact observation.

## Availability decision to freeze

Mapping identity contains immutable fields only, never availability. Each bound
reproduction must explicitly declare both mapped CAS addresses in its signed
dependencies; historical descriptors contribute no default available claim.
A new signed bound reproduction may declare missing/restricted/expired for the
same immutable mapping after actual loss. Source/test revision stays unchanged.
Conflicting current declarations reject SCVDB_OBSERVATION_CLAIM_COLLISION.

The context-free collector resolves each BoundReproduction's exact descriptors
from a bounded transitive closure. Descriptors participating in any bound record
use its explicit status. Unreferenced standalone descriptors require actual
available capture; standalone unavailable capture requires a binding batch.
Same-batch descriptors plus a truthfully unavailable bound reproduction are valid.
No incoming/resolved DTO or public capability boolean is required. Existing
collector and verify-and-pin signatures remain unchanged. Extend expansion to
prior-generation source/test records using one cumulative captured proof cache.

Opaque source bytes prove captured artifact identity, not canonical source-tree
completeness, Git identity, toolchain/device closure or executor reproducibility.
Regression must retain identical source/test mapping revisions across available
capture, actual subsequent loss, and a newly signed missing-bound reproduction.
## Migration and tests

Read old records and authenticate accepted replay without re-encoding/resealing.
Unaccepted legacy custom FAIL remains queued but cannot newly publish until its
producer supplies a new correctly signed bound revision/observation; do not mutate
the queued patch. Legacy PASS/noncustom records remain readable. V2 uses an explicit new test_definition UID; generic legacy test identities and replay remain unchanged. No silent kind conversion or global test-kind reservation.

Tests require real source/test CAS bytes with different semantic and envelope
digests; positive Reference/Paged and local settlement flows; wrong claimed map
revision, wrong source relation, wrong test revision, missing mapping, actual
corruption/false available, truthful unavailable, captured alias comparisons,
original-wire accepted replay after later loss, and unchanged HEAD on rejection.
Frozen v1 bytes/revisions must remain identical. No source fixture may substitute
repeated shapecorrect digest constants for actual artifact binding.

All test source remains UNEXECUTED until an admitted runtime exists. Streaming
large-object retention, Reference identity capture and broader reproduction
execution are not supplied by this bounded mapping transition.



## Implemented application path

observation_owner expansion now walks at most64 canonical records transitively.
Paged expansion threads the same returned query cache through every requested
alias/row layer and comparison aliases. The artifact collector checks all Bound
mapped declarations first, rejects missing declarations with
SCVDB_REPRODUCTION_ARTIFACT_UNDECLARED, then accumulates ordinary required objects.
Mapping lookup inside this already structurally validated closure uses immutable
kind/content revision (which hashes identity), rejecting divergent duplicate
records; actual alias authorization belongs to captured structural lookup.

Existing settlement prepare/reconciled-unpublished paths already invoke these
same expansion helpers; no additional settlement API or producer bypass is added.
Checkpoint Reference/Reference, Reference/Paged and Paged/Paged preservation now
shares db_checkpoint_immutable_kind, extending exact row equality from run_manifest
to all reproduction-owned kinds. Missing rows already reject in these paths.
Thus same-epoch install cannot rewrite source/test mapping rows beneath history.

All four effect planning loops consume db_paged_planning_round_limit(), replacing
independent8/12 limits that could exhaust during extra transitive alias/row proof
rounds. The shared conservative bound is138: up to64 quota-bounded discovery
layers times2 proof requests, nine fixed sites, plus the Ready observation. Valid
typed Observation->Bound->mapping closure needs at most14. Malformed signed
references still terminate with typed/quota errors; byte/key/node budgets remain
cumulative and unchanged. This bound is source-derived, not latency qualification.

A previously available artifact may later be authoritatively absent or restricted.
If its root already has a permanent reproduction pin and a nondeleted registered
entry, the existing retention owner preserves that pin and records incomplete
protection instead of rejecting the new truthful declaration. Newly requested
missing/restricted roots still fail. Corruption, unreadability, quota and scope
errors propagate. Missing-root edges are unknown, not reconstructed; the marker
blocks whole-catalog collection until actual repair verifies the full closure.

### Availability boundary acceptance oracle (2026-10-03)

REQ-019 boundary must enter both signed observation owners and reopen every
committed canonical record. Restricted uses real authenticated ciphertext;
missing uses an absent digest; expired uses a real retained observation that
passes register -> rollup -> pending deletion -> unlink at day 28. The fixture
must assert the deleted entry, actual absence and rollup digest before admitting
an immutable declaration. Editing a retention catalog into a deleted state is
not an acceptable substitute.

The content owner must report the declared unavailable state and
all_declared_available=false. Unavailable roots gain no available-evidence pin.
Accepted replay preserves the signed wire and semantic/retention heads; it does
not claim to restore evidence. This boundary is a source oracle, not a runtime
receipt or proof of complete source-tree/environment capture.

### Paged immutable mapping preservation oracle

A dropped Paged mapping must be removed consistently from the CurrentRow,
forward alias and UID reverse index. Preserve accepted batches, actor counters,
history and high-water marks; rebuild pages and manifest and independently sign
the candidate. An initialized empty receiver must actually install it and read
back all remaining records before the populated receiver is asked to reject it.
This distinguishes immutable-history preservation from ordinary malformed-index
rejection. The populated Paged path reports SCVDB_CHECKPOINT_INDEX_REGRESSION;
the Reference path reports SCVDB_CHECKPOINT_ROW_REGRESSION. Both must preserve
active and install-journal heads and original source/test mappings.

The integrated Paged regression is source-reviewed and unexecuted. Paged legacy
replay, runtime crash recovery and the selected large-scale operating profile
remain separate acceptance work.

### Fixed v1 compatibility vectors

Config, Reproduction and Observation each have a fixed typed input, literal
wire, literal domain-framed preimage and independently computed SHA256 digest.
The unit sources compare exact encoding, decoding and revision identity and
reject tampered or nonminimal variants. Vectors include multi-byte LEB128,
u64 maximum and NFC text. Expected bytes were derived from framing rules;
production encoding did not generate them. This supplies an independent oracle,
not historical binary provenance or runtime compatibility proof.

### Paged legacy replay fixture authority

The Paged legacy fixture models only an authenticated empty genesis and one
three-record v1 append batch. It applies production row, constraint, allocation
and page-update kernels and the accepted-entry derivation pinned to commit
76899528004. The same derived entry is written to batch and actor-counter indexes;
the parent history record and all alias/reverse indexes are validated by full
signed checkpoint installation. Assertions read actual installed indexes and
canonical rows before attempting replay.

This construction preserves current production admission: fresh v1 custom
failures still hit the new mapping gate, and current authorization and captured
HEAD checks still precede accepted replay. The fixture is a bounded prior-contract
model, not captured output from an old binary or equivalence with an entire old
planner. Content-loss replay, current trust revocation and stale HEAD have source
oracles; no runtime compatibility or crash-recovery result is claimed.
