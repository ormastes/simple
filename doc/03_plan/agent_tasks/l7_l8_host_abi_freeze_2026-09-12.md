<!-- codex-design -->
# L7/L8 host-ABI freeze: implementation and acceptance lanes

Date: 2026-09-12. Status: design candidate; no source/test/proof activation.
Normative [ABI/design](../../05_design/l7_l8_host_abi_freeze_2026-09-12.md)
and [immutable expected dependency bytes](../../05_design/l7_l8_host_abi_dependencies_2026-09-12.sdn).
Shared capture base: `27cc9180546a54673e1df39f504782a412223b21`.
This lane owns only those two new design artifacts and this plan. Existing
formal architecture/TLDR/plan, production files, native implementations and
SSpecs stay with their current owners. No combined dirty-worktree commit.

## Frozen dependency order

| Stage | Owner / model | Entry and deliverable |
|---|---|---|
| D0 | Common-contract source/document owners; parent merges | Admit exact 29-file manifest bytes and three referenced document baselines from owning commits; resolve absent/changed blobs and full selected import closure |
| D1 | Astra planner; independent Astra reviewer | Isolated three-document ABI candidate; static review receipt; does not open runtime gates |
| D2 | L8 host owner / Sol | Extend existing wrappers/providers with frozen V3 names; unsupported providers stay closed; every permitted namespace mutator shares the existing per-root gate |
| D3 | Existing writer/recovery/GC owners / Sol | Same-descriptor durability, exact operation recovery, complete rooted GC lease; admit issuer-bound physical receipts, not DTOs |
| D4 | G3-G6 and L7 semantic owners / Sol | Authentic live-owner scope, byte/profile verifier and affected RR closure consume D0-D3 authority; no copied grant |
| D5 | Acceptance owner / Sol then Astra | Add scenarios below, physical fault injection, pure-Simple gates, source/runner hashes, truthful receipts |
| D6 | Parent merge owner; Astra final reviewer | Integrate isolated candidates in dependency order; activation only after all real gates PASS |

D0 and D1 can proceed concurrently; implementation must bind its input to both
before dependent acceptance. D2 can author closed interfaces before D0 is
admitted, but must label its compiler closure unadmitted. D3/D4 may do isolated
planning while waiting; they cannot synthesize the missing capabilities.
Existing semantic and platform owners approve overlapping edits before work.
Luna sidecars: optional mechanical docs/index work only, no authority decisions.

## Exact SSpec names and helpers

Add to the existing cache-namespace system-test lane; intended executable path
`test/03_system/compiler/cache/l7_l8_host_abi_spec.spl`, planned manual path
`doc/06_spec/03_system/compiler/cache/l7_l8_host_abi_spec.md`.
No executable spec belongs under `doc/06_spec`. Manual output is generated only
from actual executable scenarios; no generated/ran/pass claim at design stage.

```text
setup_l7_l8_host_namespace_fixture_v3
open_l7_l8_descriptor_fixture_v3
inject_l7_l8_host_fault_v3
run_l7_l8_guarded_publish_v3
capture_l7_l8_durable_recovery_v3
check_l7_l8_exact_operation_v3
check_l7_l8_current_head_v3
check_l7_l8_descriptor_binding_v3
collect_l7_l8_complete_root_union_v3
check_l7_l8_protected_candidate_v3
check_l7_l8_scope_cleanup_v3
check_l7_l8_authority_refusal_v3
```

Setup returns a fixture owning a real temporary root, descriptor handles,
qualified provider identity, pinned immutable input generation and actual
writer receipts; it never supplies public booleans as authority. Faults are
provider-internal hooks at named syscall boundaries, not a production caller
claiming that fsync succeeded. Missing hooks/provider cause explicit refusal,
not a mock PASS. Cleanup retains any unresolved/active lease and reports the
remaining exact path; it cannot erase fixtures still owned by a child scope.

| REQ / case | Exact manual `step("...")` string | Essential oracle |
|---|---|---|
| HABI-01 | Sync the same opened immutable descriptor and its parent directory | Alias/path substitution rejected; actual descriptor success witnessed |
| HABI-02 | Distinguish selected-head replacement from directory durability | Post-rename fsync fault yields Unknown; no old-head assertion |
| HABI-03 | Hold the live reader pin through the durable publication scope | Concurrent release/GC cannot invalidate the commit loan |
| HABI-04 | Compare the expected old head separately from the target head | Valid old-to-new succeeds; target-as-old forgery fails |
| HABI-05 | Report a competing head without attributing its publication to this attempt | Competitor H visible, this operation absent, no assertion that head is G |
| HABI-06 | Recover the exact committed operation after cancellation or lost acknowledgement | Same writer/operation/generation/manifest resolves committed; no replay append |
| HABI-07 | Keep pruned or ambiguous durable history outcomes unknown | Missing/torn/pruned evidence is not Genesis or ExactNotCommitted |
| HABI-08 | Protect artifact leases readers pins and retained journal roots in one scope | Every root class contributes; omitted page/kind mapping refuses GC |
| HABI-09 | Preserve scope ownership across failed finish abort and handle reuse | Unknown/capture/finish cannot release protection; existing handles, other processes, marker failure and death cannot bypass recovery; no foreign release |
| HABI-10 | Reject hidden fourth inputs and descriptor alias substitutions | Worker actual-open trace meets cold-two/warm-three role boundary |
| HABI-11 | Reject incomplete same-generation affected reverse-reference closure | Absence/old-new domain/SCC mutants rejected before publication |
| HABI-12 | Refuse copied semantic and physical diagnostics as live authority | Forged copied packet cannot open scope or activate unverified HIR |
Use existing built-in matchers only. Until implemented, each missing step/helper
must use `fail("HABI-NN: real host evidence unavailable")` or `assert(false)`,
never `pass_todo`, no-op, unconditional true or skipped-as-pass. HABI IDs are
design obligations, not a claim that the requirements registry already issued
new REQ numbers; map to the selected parent REQs during D5. Existing L7E2E
eight names and existing live-scope helper names must not be renamed.

## Receipts and gates

Every candidate records parent/base commit, exact paths/blobs, dependency
manifest digest, source-provider/platform/filesystem identity, runner path and
hash, command, exit status, wall budget, assertions actually executed and
known unavailable gates. Dirty source and a different runtime are not an
immutable acceptance candidate. No Rust-seed fallback for Simple checks.

The implementation owner freezes concrete provider fixture/test commands
before the first run, against its admitted pure-Simple binary. Required suites
are the above SSpec, the unchanged eight-case L7 activation spec, existing
selected-head/namespace/journal/pin/lease/GC tests, and the core/lib/MCP/LSP
checks from AGENTS.md when their source surfaces are changed. Physical
fault/crash tests must use real descriptor operations and include both a
successful durable publish and each postmutation fault, not only refusals.
One test of a process crash is not a power-loss qualification claim.

For this docs-only candidate, run once: exact-path whitespace check,
manifest byte/blob validation, link existence, candidate three-path isolation,
and absence of executable `_spec.spl` files under `doc/06_spec`. No runtime
or Lean command is authorized by the design freeze. Do not rerun the prior
three capped Lean cycles; a separately scoped proof admission must be requested.

Each acceptance criterion is run at most once per session; a failing feature
has at most three fix/verify cycles. Existing PASS is not rerun. At the cap,
report the precise remaining blocker without promoting authored work to PASS.

## Handoff status

The freeze permits implementation of these exact interfaces after independent
static review. It does **not** grant production activation, semantic scope
issuance, physical publication authority or deletion permission. Medium Sol
wrapper/negative-path work is separable from difficult native/refinement work.
Merge owner: parent; final authority-bearing candidate reviewer: Astra.

## Ten implementation-only packets, 2026-09-12

This is the current launch contract. Implementation only: no validation,
proof/spec runs, generated-manual work, release/push or availability promotion.
Planner: Astra. Workers: Sol; Luna only for mechanical manifest work. Parent
owns lease handoffs and integration. Subsequent higher-model review and all
validation are separate work; authored source is not verified completion.

### Exact ancestry and observed ownership

`O = c7c5bef3ca3580ed6742dce081c697435898e2db` was observed origin/main.
`R = 877fa563005198d464784109f1fdbf84d4953a75` is the chosen reconciliation
base, combining host d13e95311b2, G756a2101283 and facet1ba1061d2be as
documented in design section 7. These short names resolve to full hashes there.
No fetch or source mutation was performed for this observation.

A read-only inventory covered 25 relevant named L7/L8/three-file/G worktrees.
The ownership-sensitive observations are:

| Worktree | HEAD / observed scope |
|---|---|
| `/home/yoon/dev/simple-l7-i12` | R; Claude reconciliation lane, tracked tree clean; P01/P03/P04/P05/P09/P10 coordination |
| `/home/yoon/dev/simple-l8-ns` | d13e95311b2; Claude retained namespace lane, P06-P08 |
| `/tmp/simple-l8-host-abi-v2-20260912` | d13e95311b2; existing Sol host lane, P06 |
| `/tmp/simple-g-production-successor-20260912` | G756a2101283; preserve existing P03/P08/P09/P10 changes |
| `/home/yoon/dev/simple-wt-g3-successor-20260910` | `e5f30f5ece5a044d3a8be4c5b800aad33c3cca7d`; dirty RR coordinator and integration spec, P05 |
| `/tmp/simple-physical-tld-threefile-20260911` | `f32e29971ec0b7f2928eb901260d41611eed1c69`; staged common physical TLD and dirty frontend index/projector, P01/P02 |
| `/tmp/simple-threefile-driver-20260911` | `d49e484251d590167c12272db9bd6a8d67064717`; dirty metadata-first route/docs/spec, P10 |
| `/tmp/simple-l7-facet-diff-20260912` | facet1ba1061d2be; existing common facet manifest must survive |

Claude PID3567704/session `0ff344d4-97f2-4d12-b531-bd6879607ef4` was busy,
cwd `/home/yoon/dev/simple`. Readable session metadata did not expose path
leases and daemon roster was empty. Neither a clean worktree nor an empty
roster proves release. **Active overlaps are analysis-only until parent obtains
explicit handoff.** This plan cannot revoke Claude or other owner leases.

### Common rules and exact path manifests

All files outside a packet's explicit list are forbidden, especially another
packet, tests, formal projects, generated/manual docs, release machinery,
credentials, gitlinks and unrelated features. Preserve existing objects,
symbols, formats and routes. No duplicate contract/grammar/journal/CAS/GC/issuer.
Existing public DTO fields, constructors and exported signatures remain
source-compatible; private state may be completed. Absent source-owner hooks
outside the list require parent reallocation, not synthetic authority.

P01 — Common contract admission.

- Own exactly the 29 `src/compiler/00.common/cache_contract/` paths enumerated
  in `doc/05_design/l7_l8_host_abi_dependencies_2026-09-12.sdn`, plus the already
  existing `src/compiler/00.common/cache_contract/semantic_facet_manifest_v1.spl`
  from R: 30 explicit manifest-selected paths, not a directory wildcard.
- Preserve/adopt existing constructors and fields for `physical_tld_v1`,
  `package_init_tld_v1`, `diagnostic_manifest_v1`, `generation_manifest_v1`,
  `reverse_reference_shard_v1`, `semantic_canonical_stream_v1`,
  `semantic_owner_revision_v1`, `semantic_query_read_manifest_v1`,
  `semantic_scope_live_port_contract_v1`, `three_payload_compile_v1/v2`,
  `three_payload_execution_v3`, `three_payload_worker_v1`,
  `virtual_source_read_registry_v1` and their existing imports. The frozen
  source-byte manifest supplies exact definitions; no new schema is selected.
- Invariants: immutable canonical DTOs only, source-owner provenance, facet
  delta preserved, no live grant constructor. Especially forbidden: frontend,
  common-lib and runtime files. The staged physical TLD remains owner-held.

P02 — Frontend TLD and semantic closure.

- Own `src/compiler/10.frontend/cache_artifact/__init__.spl`,
  `physical_tld_codec_v1.spl`, `public_summary_projector.spl`,
  `three_payload_semantic_closure.spl` in that same directory.
- Extend `FrontendThreePayloadSemanticFactV1/V2`, `ThreePayloadSemanticView`,
  `BoundSemanticInput`, `build_three_payload_semantic_refs_v1/v2`,
  `bind_three_payload_semantic_inputs`, `validate_three_payload_closure_seal_v2`,
  `semantic_refs_bound_to_physical_tld_v2` and existing codec/projector helpers.
- Bounded sealed macro/generic/default-trait bodies; ordinary trait/aspect
  calls symbolic. Especially forbidden: common physical TLD (P01), worker,
  portable verifier. Dirty index/projector need explicit immutable handoff.

P03 — Five authentic semantic scope owners.

- Own `src/compiler/35.semantics/semantic_scope_contribution_v1.spl`,
  `semantic_scope_issuers_v2.spl` in that directory; and
  `src/compiler/80.driver/cache/gateway/semantic_scope_authority_v1.spl`,
  `semantic_scope_live_owner_v2.spl`,
  `declaration_semantic_issuer_install_boundary_v1.spl` in that directory.
- Extend `SemanticIssuerAttemptContextV2`,
  `SemanticScopeIssuerEvidenceProjectionV2`, `issue_declaration_scope_v2`,
  `issue_trait_scope_v2`, `issue_aspect_scope_v2`, `issue_macro_scope_v2`,
  `issue_body_scope_v2` and existing private live-owner/install functions.
- Actual five source-owner receipts under one root/generation/profile/attempt;
  copied diagnostics never grant authority. Especially forbidden: unallocated
  `resolve.spl`, trait/macro internals and raw native hooks. Missing hooks stay
  closed and are reported with exact owner/path/signature for reassignment.

P04 — Worker descriptor broker, IO, body and admission.

- Own `src/compiler/80.driver/cache/worker/three_payload_physical_file_broker_v1.spl`,
  `three_payload_worker_io_v1.spl`, `three_payload_body_authority_v1.spl`,
  `three_payload_worker_admission_v2.spl` in that directory.
- Extend existing `ThreePayloadPhysicalFileSetV1`,
  `ThreePayloadPhysicalReadReceiptV1`, `ThreePayloadPhysicalFileEvidenceV1`,
  `read_three_payload_physical_files_v1`,
  `three_payload_physical_receipt_project_v3`, body/admission issuers without
  changing public fields/signatures. Approved additive rooted entrypoint is
  frozen in design section 7; no new common broker DTO.
- Cold-two/warm-three opened payload roles; attempts/failures/control IO
  separate; no fourth payload or worker RR access. Bytes/header/digest checks
  do not prove inode distinctness. Missing host identity support remains an
  explicit P06 dependency. Especially forbidden: frontend/common/raw externs.

P05 — Authenticated RR affected domain and atomic generation.

- Own `src/compiler/80.driver/cache/reference/reverse_reference_coordinator_v1.spl`
  and `reverse_reference_atomic_generation_v2.spl` in that directory.
- Extend `ChangedSemanticFacetV1`, `OldNewMembershipV1`, `VerifiedSccGroupV1`,
  `VerifiedAffectedDomainV1`, `VerifiedForwardManifestV1`,
  `plan_affected_queries_v1`, `plan_affected_queries_with_authority_v1`,
  `stage_reverse_delta_v1`, `old_new_membership_union_v1`, existing atomic owner.
- Same-generation forward/RR bijection, absence, old/new domain and SCC closure,
  authentic retained history. Especially forbidden: common records, generation
  publisher (P10), active owner's dirty integration spec.

P06 — Physical host namespace engine and canonical ABI owner.

- Own `src/lib/common/cache_daemon_host_authority_v1.spl`,
  `src/lib/common/cache_host_authority_v1.spl`,
  `src/compiler_rust/runtime/src/cache_daemon_host_authority_v1.rs`,
  `src/compiler_rust/runtime/src/cache_host_authority_v1.rs`,
  `src/runtime/runtime_cache_host_authority_v1.c`.
- Preserve all V1/V2 names and the five `CacheNamespace*V3` handle types/exact
  fourteen `rt_cache_host_namespace_*_v3` functions from design section 2.
  Complete physical descriptor sync/replace/dir-sync/retained recovery engine,
  not a test-only substitute. Any new identity hook requires architect freeze.
- Private handle authority, durable intent before mutation, Unknown retained,
  existing handles honor quarantine. Physical receipts do not issue semantic
  grants. Especially forbidden: compiler owner/contract files and tests.

P07 — Cooperative namespace, complete roots, leases and GC bridge.

- Own `src/compiler/80.driver/cache/gateway/cooperative_namespace.spl`,
  `cooperative_namespace_host_prerequisite_v1.spl`,
  `cooperative_namespace_gc_begin_authority_v1.spl` in that directory;
  `src/compiler/80.driver/cache/lease/lease.spl`;
  `src/compiler/80.driver/cache/gc/admission.spl`, `fast_gc.spl`,
  `mark_sweep.spl`, `reader_pin_gc_guard.spl`,
  `verified_generation_reachability_v1.spl` in that directory.
- Extend existing namespace/scope and complete-root/`CacheVerifiedClosure`
  issuers, selected-head V1 codec, lease lifecycle and GC functions.
- Same gate; include retained journal, readers, pins, manifest AND artifact
  leases; uncertain liveness retains. Decode exact V3 G/O root stream with
  count/bounds/full EOF checking. Finish/abort drain IO, preserve generation,
  never release Unknown from diagnostic capture. Especially forbidden: P06
  native/common host plumbing and P08 writer wrappers.

P08 — Journal writer, selected head and exact recovery.

- Own `src/compiler/80.driver/cache/gateway/cache_writer_v1.spl`;
  `src/compiler/80.driver/cache/journal/action_root_journal_v1.spl`,
  `checkpoint_superblock_v1.spl` in that directory;
  `src/compiler/80.driver/cache/publication/three_payload_selected_head_publisher.spl`,
  `selected_head_reopen_validation.spl` in that directory.
- Extend `CacheWriterCommitOutcomeV1`, `CacheWriterDurableReceiptV1`,
  `CacheWriterDurableHeadV2`, `cache_writer_capture_durable_head_v2`, existing
  GC-window wrappers, `ThreePayloadSelectedHeadExpectationV1`, additive
  `ThreePayloadSelectedHeadTransitionV3` from the ABI freeze.
- Expected OLD distinct target NEW; exact durable prefix/operation/object
  identities; authentic recovery owner only; no Unknown rollback or assumed
  old head after competitor wins. Especially forbidden: codec(P07), raw host
  (P06), generation packet/coordinator(P10).

P09 — Portable byte/profile semantics and verified CAS.

- Own `src/compiler/20.hir/portable_body_budget.spl`, `portable_body_graph.spl`,
  `portable_body_profile_types.spl`, `portable_body_semantics.spl`,
  `portable_object_profile_v1.spl` in that directory;
  `src/compiler/35.semantics/portable_body_effects.spl`;
  `src/compiler/80.driver/cache/cas/__init__.spl`,
  `verified_cas_kind_registry_v1.spl`, `verified_cas_store.spl` in that directory;
  `src/compiler/80.driver/cache/native_object_publication_decision_v1.spl`.
- Extend `VerifiedCasKindVerificationV1`, `verified_cas_verify_kind_bytes_v1`,
  `verified_cas_verify_portable_hir_bytes_v1`,
  `verified_cas_verifier_registry_digest_v1` and existing portable constructors.
- Actual decoded bounded bytes/profile/effect semantics, immutable verified
  identity; unsupported HIR/advice refused. Especially forbidden: common
  portable reference, frontend grammar, worker and native loader owners.

P10 — Closure packer, generation publisher and driver composition.

- Own `src/compiler/80.driver/cache/closure/three_payload_closure_packer.spl`,
  `three_payload_closure_packer_v2.spl` in that directory;
  `src/compiler/80.driver/cache/publication/three_payload_generation_publisher_v1.spl`;
  `src/compiler/80.driver/cache/gateway/cache_gateway_adapter.spl`;
  `src/compiler/80.driver/cache/metadata_first_driver_route.spl`.
- Extend `ThreePayloadImmutableObjectV1`, `ThreePayloadGenerationPrepareInputV1`,
  `PreparedThreePayloadGenerationV1`, `ThreePayloadDurablePublicationPacketV1`,
  `prepare_three_payload_generation_v1`, `publish_verified_three_payload_generation_v1`,
  existing exact-operation resolver, packer and driver-route constructors.
- Genuine P01-P09 authorities compose at one coordinator; publish summary,
  scope, forward reads, RR and object roots together; preserve prior routes.
  Especially forbidden: authority definitions in P03/P06/P07/P08 and every
  unowned compiler source file. Metadata-first dirty lane stays analysis-only.

### Dependency and merge ledger

P01 supplies unchanged common records to every packet; its commit is pending,
not a fabricated SHA. P02 supplies projected TLD/body facts; P03 authentic
scope; P06 physical capability; P07 complete roots; P08 durable publication;
P09 verified portable bytes. No consumer substitutes its own definition.

| Packet | Required predecessor implementation | Start state / expected ancestry |
|---|---|---|
| P01 | Existing D0/facet source-owner candidates | Analysis now; edits after common-owner handoff. R -> P01 |
| P02 | P01 | Analysis-only dirty frontend overlap; then R+P01 -> P02 |
| P03 | P01 and actual source-owner hooks | Analysis-only Claude R/G claim; after release R+P01 -> P03 |
| P04 | P01; frozen P02/P03 interfaces; P06 identity hook for alias authority | Analysis-only Claude R claim; after release may author R child; compose after predecessors |
| P05 | P01/P03 | Analysis-only active dirty RR; then R+P01+P03 -> P05 |
| P06 | Existing d13e host candidate and frozen ABI | Analysis-only active Claude/Sol host claim; after release d13e successor or R child |
| P07 | P01/P06 | Analysis-only namespace lease and predecessors; R+P01+P06 -> P07 |
| P08 | P01/P06/P07 | Analysis-only namespace/G lease and predecessors; accumulated prefix -> P08 |
| P09 | P01; frozen P02/P03 semantic interfaces | Analysis-only Claude R/G claim; after release independent R+P01 child |
| P10 | P01-P09 and retained metadata-first route delta | Analysis-only until predecessor commits and route-owner handoff; accumulated prefix -> P10 |

All packets can immediately do bounded read-only implementation analysis.
Source edits require explicit parent handoff of active overlaps. Parent may
release unaffected files independently; that does not release dirty neighbors.
After handoff P01/P03/P04/P06/P09 can author independent compatible deltas;
P02/P05/P10 first reconcile dirty owners; P07/P08 consume actual predecessors.

Parent creates immutable `I0` by reconciling O and R while preserving both
feature sets. I0 does not yet exist in this docs task. Owned-path R-based
commits may be prepared after handoff, then ported as exact deltas onto I0;
never merge a stale whole tree. Deterministic order:
`I0 -> P01 -> P06 -> P02 -> P03 -> P09 -> P04 -> P05 -> P07 -> P08 -> P10`.
Every packet receipt names exact ancestry, owned paths, consumed dependency
commits, preserved symbols and remaining implementation holes. No task may
silently expand the allowlist or infer production authority from this plan.

## Final eight-packet coding wave: V4 ports, defaults and unit seams

Normative declarations, fields, constructors, cases and method signatures are
in design section 8. This pass allows writing local algorithms and tests before
authentic providers exist. It does not authorize implementation/validation in
the current docs task, or production gate changes in subsequent coding tasks.
All existing production defaults stay unavailable. No fake/provider flag is a
substitute for live owner authority. U01-U03 author tests; execution is deferred.

Exact dependency bases:

- `B1 = 97eafe76f48feb3e3ac252130677a35cc3d8b77d` (P01 common-contract candidate).
- `B7 = 5b8c41c25e6d4d0dfc0ac041a783fd4adc52ee65` (reviewed P07 capture-only
  successor, based on `4cd0864511e`; no deletion authority).
- Existing P08 unit-only candidate `bd68b00bf8e707126bba08900f9655452a9854e4`
  is preserved as another owner's evidence; no blanket adoption or rewrite.
- Observed upstream during this freeze:
  `88a05e3bed8dbd5b70a436c568fa753e550c474c`; not substituted for these bases.

The five production allowlists are the exact P03/P05/P07/P08/P10 lists above,
with **one explicit addition/reassignment**: P03 alone now owns
`src/compiler/00.common/cache_contract/semantic_scope_live_port_contract_v1.spl`
for the shared V4 vocabulary. P01's other 29 existing paths stay out of scope.
No new source file or duplicate common contract is permitted. Tests are not
owned by production packets. Every unlisted path, native ABI change, push,
release or generated/manual update remains forbidden.

| Packet | Exact paths / defining responsibility | Base and dependency order |
|---|---|---|
| P03 | Its five existing source paths above plus the one common live-port path; shared V4 enums/records, scope/hook traits, closed adapters, registry scaffolds and owner-returning acquire runner | B1; shared vocabulary commit first, then scope/hook implementation. No live-token issuance from defaults |
| P05 | Existing `reference/reverse_reference_coordinator_v1.spl` and `reverse_reference_atomic_generation_v2.spl` only | B1 + P03 vocabulary; trait/closed adapter/RR core runner may be coded without live scope |
| P07 | Its exact nine namespace/lease/GC source paths above; namespace trait/default/root capture and unavailable transitive-closure seam | B7 + P03 vocabulary; preserve reviewed removal of copied-receipt deletion and unsafe lease projection |
| P08 | Its exact five writer/journal/selected-head paths above; public V4 trait/receipt/default live only in `three_payload_selected_head_publisher.spl` | B1 + P03 vocabulary; commit signature includes namespace, scope, affected and closure tokens; no new writer/generation import cycle |
| P10 | Its exact five closure/generation/adapter/route paths above; new V4 composition declarations only in `cache_gateway_adapter.spl` | B1 + P03/P05/P07/P08 interface commits; core port composition can proceed before authentic adapters |
| U01 | `test/01_unit/compiler/cache/fixtures/l78_scope_rr_ports_v4.spl`; `test/01_unit/compiler/cache/l78_scope_port_v4_spec.spl`; `test/01_unit/compiler/cache/l78_affected_domain_port_v4_spec.spl` | B1 + P03/P05 interfaces; owns scope/RR fake classes, factories and expectation helpers only |
| U02 | `test/01_unit/compiler/cache/fixtures/l78_namespace_publication_ports_v4.spl`; `test/01_unit/compiler/cache/l78_namespace_port_v4_spec.spl`; `test/01_unit/compiler/cache/l78_publication_port_v4_spec.spl` | B7 + P03/P07/P08 interfaces; owns namespace/publication fake classes, factories and expectation helpers only |
| U03 | `test/01_unit/compiler/cache/fixtures/l78_pipeline_ports_v4.spl`; `test/01_unit/compiler/cache/l78_pipeline_ports_v4_spec.spl` | B1 + four port interfaces + P10 core + U01/U02 fixtures; imports other fake definitions, never copies/redefines them |

All fixtures implement exact section-8 traits using `me`, return or retain
updated owner state, and issue TestDouble tokens only. No test imports a raw
host mutation API or writes an actual cache to simulate success. Positive
model transitions and distinct negative cases must be exercised; asserting
only that the production gate is false is not core-behavior coverage.

Unit seams cover: scope issuer/dimension/foreign/stale/expired/revoked tokens;
RR missing absence/SCC/old-new membership and wrong generations; canonical
namespace root capture, missing artifact roots, truncated stream and retained
Unknown finish/abort; precommit conflict versus postcommit Unknown/exact
resolution; pipeline order, early refusal, cancellation, returned owner state
and no test-token crossing into production. No unit result is host proof.

Launch now after relevant lease release: P03 shared declarations first; other
production/unit owners can prepare exact interface-dependent code concurrently,
but must consume the committed shared types before integration. Live dependency
availability is not a coding prerequisite. Gate false is not a reason to skip
the pure core. If a compiler cannot express the planned generic trait runner,
report the exact syntax limitation; do not change the frozen API silently.

Merge order: P03 shared vocabulary -> P03 scope hooks -> P05/P07/P08 interface
and core deltas -> U01/U02 fixtures and unit specs -> P10 core -> U03 pipeline
fixtures/spec. Parent records an actual reconciled integration base and ports
only each owned delta, preserving current-main/Claude changes. Existing leases
remain effective until explicit handoff; this document is not a lease release.
No implementation or test execution is claimed by this design commit.

Final interface spelling amendment: design section 8.8 replaces reserved
`namespace` with `namespace_port` for the P10 field/U03 factory and
`namespace_token` for P08 parameters. Event strings and positional contracts
remain unchanged. P10 authored candidate is `8eef058617d5e7903347da9f49a1a46b23fda18d`
on parent `1826de9ba29ae5f54689f3f8d534f948956e4fe3`; only gateway composition
was changed. It still requires corrected versioned P05 token-plus-plan and
final P03/P07/P08 commits before integration. No runtime validation is claimed.
Pure packers retain existing data APIs and never mint namespace closure
authority; generation publisher must not import its selected-head consumer.
