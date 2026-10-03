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
