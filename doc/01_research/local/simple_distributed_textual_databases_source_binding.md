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
