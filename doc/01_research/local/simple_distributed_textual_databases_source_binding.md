# REQ019 source/test binding local research

Base76899528004; isolated work/item2-source-binding-20261003. No runtime probes.
Selected requirements unchanged. Existing design section8 distinguishes semantic
revision, SourceSnapshotRef and ObjectRef. db_evidence defines unused
DbTestDefinitionRevision(reference,definition_digest); reproduction source_revision
is text. db_reproduction_codec currently encodes three immutable v1 variants.
observation_content verifies effective/invocation/payload CAS and dependencies,
but neither source nor test actual mapping. Current fixture test kind is test.

Existing owner paths: Reference/Paged commands -> observation_owner -> actual
captured structural planners/lookups -> content inspector -> same-catalog pins ->
final recheck -> semantic CAS. Settlement uses the same content owner before
prepare and after uncertain publication is proven absent. Accepted replay must
remain before present-day artifact validation and preserve original signed wire.

Core review: generic test kind must not be reserved silently. Explicit new v2
kind test_definition preserves legacy test identities without migration. New
source mapping semantic digest must not pretend to verify a Git/source tree hash:
opaque CAS bytes establish only exact captured artifact mapping. Existing compile
source inventory distinguishes snapshot_manifest_digest/source_inventory_digest;
this proposal does not replace their domains or claim tree completeness.

Implementation must extend transitive prior-generation lookups/proof rounds,
not just same-batch records. Preserve v1 encoding/hash exactly. Remaining bounds
256nodes/8MiB pin objects and separate proof/catalog IO are explicit. Existing
Reference alias limitation and large-object target remain open.

Owners: this lane research/design and source after freeze; core compatibility
review; evidence fixtures/specs after freeze. Exact proposed contract is in
simple_distributed_textual_databases_source_binding.md under doc/05_design.

### Actual expiry evidence follow-up (2026-10-03)

Local inspection found observation_content._observation_inspect recognizes
expired only for absent bytes backed by a deleted retention entry, an unlink or
synced-absence receipt, nonempty rollup digest and age at least 28 days. The
existing false-expired regression had no positive real-deletion counterpart.
The new expired observation fixture drives db_retention_run over an actual
encoded retention observation before signing the config/reproduction/observation
chain. No production change is implied by this test gap.

The read-only runner audit still found no C:/dev/simple/bin/release directory.
The inherited SCV hello diagnostic reports terminal exit 1 and empty admission;
the provisional startup diagnostic reports terminal exit 88. Neither is a
verified live wait or an admitted full runner. No binary was executed here.

### REQ-017 owner-path audit after binding coverage

The selected observation identity contract is broader than signed batch replay.
The exported db_observation_admit pure helper is only called by unit tests;
Reference/Paged effect admission does not compare independently allocated rows
by provider tuple. The typed codec validates names declared by the incoming
record itself, not an independently admitted capability schema. This leaves
provider scope and cross-UID reuse unenforced despite valid source/test binding.

The concrete regression and completion obligations are recorded in
../../08_tracking/bug/item2_provider_identity_owner_gap_2026-10-03.md.
An authenticated fresh-UID collision source now targets the effect owners;
its expected failure has not been executed. Existing REQ-017 system cases stay
explicit fail-fast rather than inheriting proof from accepted-batch replay.

A fresh bounded runner audit found admission NONE for the inherited-core40
candidate; its test-runner receipt is terminal exit 1. The exported bootstrap
path contains simple.exe.rejected and the main bin/release path is absent.
A RUNNING label elsewhere in the aggregate status is not evidence of a live
handle or usable runner. No binary was executed or restarted by this lane.

### Capability-pinned identity kernel implementation contract

Independent review confirms DbCiCapabilities lists the five built-in provider
fields while DbProviderIdentity.dimensions holds only extras. Passing one list
as the other would reject valid records or let incoming names choose their own
scope. Existing pure identity comparison includes the observation reference in
content, so it cannot deduplicate independently allocated import UIDs. The new
comparison must exclude only that own reference while validating it and retaining
all nested/contextual references and result fields.

The new design records canonical-name collision checks, explicit case identity,
full-policy-key migration and authenticated index readback. Canonical v1 encoding
is a compatibility boundary, not a place to silently change historical bytes.
Any new content comparison has its own domain. This research justifies a pure
kernel first; the known owner/index/quarantine defect remains open until the
same contract is integrated across Reference, Paged, settlement and checkpoints.

### Persistence and mixed-batch owner research

IdentityMap rejects duplicate alias sequences, so it cannot silently redirect a
second proposed observation UID to an existing one. File identity correction
logs are a separate subsystem, not an atomic DB equivalence proof. A full
mixed-batch duplicate implementation needs versioned immutable links, consistent
nested-reference/precondition resolution and atomic publication with accepted
state and other operations. A plain skipped append would leave dangling UIDs.

Quarantine import already stores and reopens exact signed bundles in controlled
CAS. It does not publish canonical observation-conflict decisions. The final
quarantine receipt must bind that object to a rechecked generation/policy/index;
separate store channels remain separate commits even under one SJ lease. This
means decision publication may change HEAD without changing accepted observations
or counters. The initial regression's whole-store equality was too strict and
has been replaced with actual accepted-projection checks after independent review.

Compact identity entries should retain only claim/reference data, then verify
against actual original records. Repeating full observations in every index
entry would add unnecessary persistent bytes against Operating B growth targets.
Canonical codec success alone is not authenticated membership or absence.

### Direct-wire quarantine preparation

The existing quarantine file owner already parses canonical bundles before
calling db_evidence_store_put. Extraction of that final validated-wire operation
allows a future identity owner to preserve original rejected bytes without an
extra temporary input file. Guarded file import remains a separate input adapter.
The lower evidence store owns one short SJ lease, private publication staging,
readback and directory durability; a caller must prepare outside its final
decision lease to avoid nesting. The stored envelope excludes accounting day
from content identity, so a handle's day is caller provenance, not signed time.
No new signature authority, accepted state or decision journal is supplied by
this extraction. Canonical ASCII wire makes the delegated UTF-8 wire hash equal
to the original guarded file-byte hash.
