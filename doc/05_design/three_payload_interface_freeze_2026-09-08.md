<!-- codex-design -->
# L7 three-payload interfaces and ownership freeze

Date: 2026-09-08. Status: reviewed planning/interface baseline; new DTOs/ports
below are proposed, not implemented, production-accepted, or admission
authority. Merge owner: Astra. Any later production/admission acceptance needs
independent implementation evidence and review; this baseline itself cannot
provide it. Implementation sublanes wait for this interface review.

## Compatibility audit: what must not be promoted unchanged

Current `three_payload_compile_v1.spl` checks nonempty digest strings and
caller-supplied read counts; its seal has no physical section ownership,
complete semantic coverage or trusted IO receipt. The driver packer currently
serializes textual sections into a separate combined canonical payload and
remaps global indices. That is model/packer evidence, not proof of three
physical worker inputs. Keep its V1 tests and names; do not reinterpret V1
bytes or quietly make the existing struct mean the stronger contract.

`three_payload_publish_host_admitted_v1` is disabled. It also calls legacy
`result_manifest_put`, which writes an action-keyed lookup path before journal
admission. A future host commit capability alone is insufficient to enable
this existing sequence. Split immutable blob preparation from action/root
admission, and project lookup state only after the admitted journal receipt.
The complete seal/ref/completeness identity must be bound to the action; a
digest of section bytes alone cannot authenticate mutable seal metadata.

Existing `PublicSummaryV1`, canonical codec generator, HIR codec, SMF/container,
semantic external-effect `SemanticReadSetV1`, AOP index, native/device catalogs,
PureDatabase projection, CAS and journal retain their owners and meanings.
Macro/body embedding does not turn a public summary renderer into a private
source publisher. Package-initializer runtime effects still execute through
the existing initialization owner, not during ordinary header inspection.

## Exactly which three payloads

| Role | Worker content | Preparation and identity |
|---|---|---|
| `Source` | changed module `.spl` frozen bytes | Always present, one distinct source payload; never compiler-modified |
| `PriorModuleTld` | original prior-generation module `.tld`, cutoff/reusable facts | Optional only for cold/new file; do not rewrite it to fabricate a current dependency or use the new output header as its own input |
| `PackageInitTld` | sealed effective `__init__.tld`, including indexed imported facts/body sections required now | Always present; coordinator constructs current task closure before worker admission, retaining original semantic-object identities |

Newly required facts absent from the prior header go into the sealed initializer
payload, not a fourth pack file. A prepared initializer can be a task-qualified
physical projection with shared content-addressed chunks; it is not a new
source package or a mutable global replacement. All consumed bytes must already
be in the admitted file object; external chunk fetch inside the worker is an
extra input and requires typed fallback before claiming three-payload success.

Three means distinct admitted input objects/files, not exactly three `read` or
`pread` syscalls: indexed lazy decoding may read several ranges of each file.
Record distinct inputs, opens, syscalls, bytes and decoded sections separately.
Catalog/inventory/RR preparation, target lowering, linking and runtime startup
have separately reported input counts. A warm worker has three; cold has two.
No RR file, cache handle, network handle or ambient filesystem authority crosses
the worker boundary. A closure miss returns a typed fallback request; the owner
chooses and labels a new profile rather than letting the worker open a fourth.

Macro/CTFE and consumed generic/default-trait bodies are indexed embedded bytes
in a TLD input. Ordinary concrete trait calls and call-only aspect advice carry
signature, effects, ordering/selection and symbolic immutable callable/object
identity, not advice implementation bytes. Inlining/body-sensitive features
require an embedded body or explicit fallback. RR schedules affected owners;
it neither owns nor injects macro/advice content.

## Common DTO ledger: one file owner, no parallel redeclarations

Paths below are relative to `src/compiler/00.common/cache_contract/` unless
specified. All new records use existing canonical encoding, strict digest
validation and stable IDs. Text IDs are semantic identities, not paths to open.
Each decoder rejects unknown mandatory semantics, arithmetic overflow and
out-of-bounds/overlapping sections before allocation. Optional presentation
fields remain losslessly skippable. New V2 seal schema has separate keys.

| Exact file (proposed unless marked existing) | DTOs and mandatory fields |
|---|---|
| `three_payload_compile_v1.spl` (existing) | Existing V1 refs/seal/counters/errors unchanged; compatibility/model surface, not stronger admission |
| `physical_tld_v1.spl` | `TldPayloadRoleV1 = PriorModuleTld | PackageInitTld`; `TldSectionRefV1{role, section_index:i64, kind:text, semantic_object_digest:text, offset:i64, stored_bytes:i64, decoded_bytes:i64, encoding_profile:text}`; `PhysicalTldHeaderV1{schema:i64, role, semantic_record_digest:text, section_table_digest:text, payload_bytes:i64, sections:[TldSectionRefV1]}` |
| `package_init_tld_v1.spl` | `PackageInitTldV1{package_id:text, parent_scope_digest:text?, membership_root_digest:text, ordered_member_ids:[text], aspect_root_digest:text, trait_root_digest:text, macro_root_digest:text, extension_root_digest:text, template_root_digest:text, initializer_contract_digest:text, ordered_initializer_refs:[text]}` |
| `semantic_query_read_manifest_v1.spl` | `SemanticQueryKeyV1{kind:text, stable_entity_id:text, semantic_profile_digest:text, parameter_digest:text}`; `SemanticQueryReadV1{producer, consumer, facet:text, ordinal:i64, consumed_fingerprint:text, witness_digest:text, partition_id:text, completeness:SemanticCoverageV1}`; `SemanticQueryReadManifestV1{schema:i64, consumer, ordered_reads:[SemanticQueryReadV1]}`; `SemanticCoverageV1 = Complete | Conservative | Unknown` |
| `reverse_reference_shard_v1.spl` | `ReverseReferenceEdgeV1{producer, facet:text, consumer, consumed_fingerprint:text, forward_manifest_digest:text, partition_id:text}`; `ReverseReferenceShardV1{schema:i64, partition_id:text, coverage:SemanticCoverageV1, sorted_edges:[ReverseReferenceEdgeV1]}`; `ReverseReferenceDeltaV1{consumer, old_manifest_digest:text?, new_manifest_digest:text, inserted:[ReverseReferenceEdgeV1], removed:[ReverseReferenceEdgeV1]}` |
| `portable_object_ref_v1.spl` | `PortableObjectStageV1 = Base | Composed`; `PortablePortabilityV1 = Portable | TargetFamily | TargetExact`; `PortableObjectRefV1{content_digest:text, stage, portability, ir_schema:i64, required_semantics_digest:text, target_contract_digest:text?, verification_receipt_digest:text}`. Existing planned `PortableBaseSioV1`/`PortableComposedSioV1` remain SMF profiles owned by HIR/portable verifier, not duplicate IR nodes here |
| `generation_manifest_v1.spl` | `GenerationManifestV1{schema:i64, snapshot_digest:text, catalog_digest:text, summary_refs:[text], scope_refs:[text], rr_shard_refs:[text], forward_manifest_refs:[text], portable_refs:[PortableObjectRefV1], target_refs:[text], diagnostic_refs:[text]}`. No own final digest field; outer canonical digest computed afterward |
| `three_payload_compile_v2.spl` | `ThreePayloadSemanticRefV2{kind:ThreePayloadSemanticRefKindV1, stable_entity_id:text, callable_signature_digest:text, effect_digest:text, body_or_object_digest:text, embedded:TldSectionRefV1?, selection_contract_digest:text}`; `ClosureCoverageRootV1{dimension:text, root_digest:text, coverage:SemanticCoverageV1}`; `ThreePayloadClosureSealV2{schema:i64, input_generation_digest:text, snapshot_digest:text, source_digest:text, prior_tld_digest:text?, init_tld_digest:text, compiler_semantics_digest:text, consumed_inputs_digest:text, semantic_refs:[ThreePayloadSemanticRefV2], coverage_roots:[ClosureCoverageRootV1], section_count:i64, payload_bytes:i64, max_decode_bytes:i64}` |
| `three_payload_worker_v1.spl` | `ThreePayloadInputIdentityV1{source_digest:text, prior_tld_digest:text?, init_tld_digest:text, seal_digest:text}`; `ThreePayloadReadReceiptV1{input_identity, executor_digest:text, distinct_source:i64, distinct_prior:i64, distinct_init:i64, external_input_count:i64, rr_input_count:i64, open_calls:i64, read_calls:i64, read_bytes:i64, decoded_sections:i64, peak_decode_bytes:i64, denied_io_attempts:i64}`; `ThreePayloadWorkerResultV1{input_identity, new_summary_digest:text, query_reads:SemanticQueryReadManifestV1, portable_refs:[PortableObjectRefV1], diagnostic_digest:text, read_receipt:ThreePayloadReadReceiptV1}` |

V2 semantic refs retain the V1 kind distinction: required executable bodies
must have `embedded`; ordinary call-only trait/aspect refs must not. A section
ref addresses one role-specific final section table, never the V1 global
combined-pack index. Use original semantic body identity independently of
packing offsets. `selection_contract_digest` binds activation/order/trait
choice; it is not a substitute for complete membership/absence witnesses.

Coverage dimensions are a closed schema set: membership, resolution absence,
trait candidates/coherence, macro/CTFE inputs, generic bodies, extensions,
aspects/pointcuts, initialization, configuration and overlays. Unknown coverage
refuses the strict profile. Conservative work is allowed only when its bounded
complete candidate domain is sealed and produces the same result as a clean
build. Watcher silence or an empty RR result is never a completeness proof.

The runtime/broker issues the read receipt from actual restricted accesses;
caller-filled numbers do not authorize admission. Public DTOs are data, not
capabilities. The seal is authenticated by an admitted coordinator generation
and verified original object closure. `seal_digest` is computed from canonical
seal bytes, not included recursively inside that seal. Input generation is
the admitted parent; output generation is computed after returned artifacts
and read deltas, avoiding hash cycles.

## Exact executable port ownership

| Owner file | Port to freeze | May not own |
|---|---|---|
| `10.frontend/cache_artifact/public_summary_projector.spl` (existing) | Existing `project_public_summary_v1(PublicSummaryProjectionInputV1)` and readable renderer; emit canonical public facts only | IO, RR updates, target layout binding, private-body extraction into public text |
| `10.frontend/cache_artifact/physical_tld_codec_v1.spl` (new) | `encode_physical_tld_v1(header, canonical_sections) -> Result<[u8],...>`; `decode_physical_tld_index_v1(bytes, bounds) -> Result<PhysicalTldHeaderV1,...>`; reuse common codec and existing summary renderer | A second summary extractor or action publication |
| `80.driver/cache/closure/three_payload_closure_packer_v2.spl` (new) | `seal_three_payload_closure_v2(snapshot, parent_generation, module, verified_objects, bounds) -> Result<PreparedThreePayloadV2,ThreePayloadFallbackV1>`; private `PreparedThreePayloadV2{seal, source_bytes:[u8], prior_tld_bytes:[u8]?, init_tld_bytes:[u8]}` | Raw writes, a fourth combined worker payload, RR graph mutation |
| `80.driver/cache/reference/reverse_reference_coordinator_v1.spl` (new) | `plan_affected_queries_v1(changed_facets, old_new_membership, verified_forward_manifests, rr_shards) -> AffectedQueryPlanV1`; `stage_reverse_delta_v1(old_reads,new_reads) -> ReverseReferenceDeltaV1` | Macro/advice bodies, worker IO, overriding AOP/trait semantics |
| `80.driver/cache/worker/three_payload_worker_io_v1.spl` (new) | Private confined payload handles; `run_three_payload_worker_v1(prepared_handles, verified_seal, policy) -> Result<ThreePayloadWorkerResultV1,ThreePayloadFallbackV1>`; trusted counted section reads | CAS/journal/DB/network/ambient path access, self-issued IO receipts |
| `20.hir/hir_codec.spl` plus `20.hir/portable_object_profile_v1.spl` (new profile adapter) | Encode/verify existing HIR as Base or Composed SMF sections; return `PortableObjectRefV1` | New HIR/MIR hierarchy, treating LLVM bitcode/native SMF as universally portable |
| `80.driver/cache/publication/three_payload_generation_publisher_v1.spl` (new) | Prepare immutable generation objects; admit through existing writer's future mutation-scoped host call; return verified generation receipt | Early `result_manifest_put`, SQL authority, changing feature/body selection after verification |
| `80.driver/cache/gateway/cache_writer_v1.spl` + `lib/common/cache_daemon_host_authority_v1.spl` (existing) | Consume proposed `CacheCommitFrameV1`/`CacheCommitReceiptV1`; the referenced local/untracked historical `cache_writer_mutation_scope.md` is unavailable as repository evidence. The inline contract is host-only validated-frame commit, durable journal before receipt, and no authority from readiness/caller-filled receipt/legacy `result_manifest_put`. | Treat readiness as authority or enable the current legacy publication sequence |

`ThreePayloadFallbackV1` reasons are frozen as `ExternalFacetRequired`,
`ExternalBodyRequired`, `MembershipIncomplete`, `WitnessIncomplete`,
`ScopeGenerationMismatch`, `BoundsExceeded`, `UnsupportedSemantics`,
`CorruptPayload`, `AuthorityUnavailable`. Corruption is not absence. Owner-side
fallback preserves the frozen source snapshot and reports additional reads.
`AffectedQueryPlanV1` remains driver-private: ordered query IDs, owner modules,
changed dimensions, conservative-domain receipt and SCC group identities.

## Dependency DAG and three-worker rollout

```text
G0 Astra interface review + common DTO/golden fixture freeze
 ├─ G1 Sol: physical TLD codecs/projector adapter
 ├─ G2 Sol: forward-read/RR coordinator + membership integration
 └─ G3 Astra: mutation-scope host design + confined worker port review
G1 + G2 -> G4 Astra: V2 closure preparation (source + optional prior + init)
G4 + confined IO -> G5: source-driven 2/3-input worker parity and truthful counters
HIR portability verifier + G5 -> G6: Base/Composed SIO reference integration
G2 + G5 + G6 + admitted mutation authority -> G7: atomic generation publication
G7 + crash/concurrency/Stage2+Stage3 matrix -> G8: qualified default/release
```

There are only three implementation/review slots plus the scheduling root.
Common DTO files have one Astra owner. G1 owns only its codec/projector files
and mirrored tests; G2 owns only reference coordinator/adapters and mirrored
tests. Shared AOP/trait/semantic leaves require explicit handoff to their
existing owner, not simultaneous edits. G3 is design/IO review until native
authority scope is approved; Windows/SimpleOS remain fail-closed. Refill idle
slots with independent tests/fixtures, not overlapping common schema changes.
G4–G7 are sequential when they touch the same driver/compiler owner. Do not
start implementation sublanes until Astra/root accept G0.

## Acceptance and isolated review workflow

G0: exact DTO/port/file inventory, version migration and positive/negative
golden fixture ownership approved; no new successful stub exports. G1: bounded
binary round-trip, unknown mandatory/optional behavior, original-object digest
preservation. G2: add/remove/zero-match, membership/absence, helper completeness,
old/new candidate union, deleted reads and SCC atomicity. Existing substring
pointcut masks cannot establish complete typed reads.

G5 must trace actual source-driven cold/warm worker IO: two/three distinct input
files, zero external/RR reads, bytes/sections/bounds and denied fourth-input
attempts. Capability confinement must cover direct/foreign IO and compile-time
code, not merely omit a path field in a DTO. Semantic outputs/diagnostics must
match a clean full-source compile. G6 checks symbolic layouts, effects, generic
and trait bodies, call-only advice, native-loader refusal and target separation.
G7 requires real concurrent revoke/commit, durable retry/recovery, failure before
any lookup visibility, DB rebuild and reader/GC protection. Model 7/7 and packer
4/4 remain explicitly insufficient for production activation.

Current user authorization permits pushing completed lanes and approving their
PRs. Execution remains conditional: isolate exactly one lane in its own
worktree/branch, preserve unrelated dirty files, include its source/spec/docs,
run declared checks once, obtain Astra semantic/ownership review and independent
evidence review, then commit/push only that reviewed lane and create/update its
PR. Review the exact remote head/diff and required checks before approval; any
new commit invalidates prior approval evidence. Do not infer authorization for
force-push, bypass, unrelated changes, release or deployment.

Use the repository sync/verification skills for actual commit/push operations;
this design task performs none. A model/docs lane may be marked scoped PASS
without calling the runtime implemented. Production lanes require their native
and admitted-runtime gates; partial/blocked lanes are not completion PRs. If
GitHub prohibits author self-approval, retain the exact refusal, leave approval
pending and request an independent authorized reviewer. Never switch identities
or credentials to evade the platform rule. Merge remains gated by required
checks, review and the root's integration policy.
