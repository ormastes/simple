# Detail design: generic RR facets and HIR-variant object keys

Lane `generic-rr-hir-variant-obj`. Architecture: `doc/04_architecture/generic_rr_hir_variant_obj.md`.

## 1. `generic_tldr_view_v1.spl` additions (owner module)

```simple
pub val GENERIC_FACET_DIMENSION_V1 = "generic"
pub val GENERIC_FACET_SIGNATURE_V1 = "generic.signature"
pub val GENERIC_FACET_BOUND_V1 = "generic.bound"
pub val GENERIC_FACET_BODY_V1 = "generic.body"

pub struct GenericBoundV1:
    param_index: i64
    bound_key: text          # structural key of the bound (trait/type), never display text

# GenericTemplateEntryV1 gains two TRAILING defaulted fields (positional seed fill safe):
    bounds: [GenericBoundV1] = []
    body_digest: text = ""   # sha256 hex of the single erased body; "" = no body

pub struct GenericTemplateFacetsV1:
    template_id: text
    signature_fingerprint: text   # 64-hex sha256 (three_payload_contract_digest_valid_v1)
    bound_fingerprint: text
    body_fingerprint: text

pub struct GenericFacetChangeV1:
    facet: text
    old_fingerprint: text?        # nil at genesis
    new_fingerprint: text?        # nil when the template is removed

pub fn generic_template_signature_fingerprint_v1(entry) -> text
pub fn generic_template_bound_fingerprint_v1(entry) -> text
pub fn generic_template_body_fingerprint_v1(entry) -> text
pub fn generic_template_facets_v1(entry) -> GenericTemplateFacetsV1
pub fn generic_template_changed_facets_v1(old: GenericTemplateEntryV1?, new: GenericTemplateEntryV1?) -> [GenericFacetChangeV1]
pub fn generic_caller_consumed_facets_v1() -> [text]      # [bound, signature] sorted
pub fn generic_template_consumed_facets_v1() -> [text]    # [body, bound, signature] sorted
pub fn generic_bounds_valid_v1(entry) -> bool             # indices in range, keys non-empty
```

Fingerprints:

- signature = `sha256(frame("generic-facet-signature/v1") + frame(summary_digest))`
- bound = `sha256(frame("generic-facet-bound/v1") + frame(n) + for b in sorted(bounds): frame(index) + frame(key))`
  (sorted by `(param_index, bound_key)`, duplicates removed); with no bounds it is a fixed
  non-empty digest, so "no bounds" -> "one bound" is a change.
- body = `sha256(frame("generic-facet-body/v1") + frame(body_digest))`.

`generic_template_changed_facets_v1` returns facets in sorted facet-name order; an entry is
emitted only when the fingerprint text differs. `(nil, nil)` -> `[]`. Bounds and
body_digest are part of the sealed section body (`_entry_body_v1`) and are decoded strictly:
a bound index outside `0..params.len()` or non-numeric fails the decode (`"bad bound"`).
Sections encoded before this change fail to decode (fail closed, cache miss), which is the
intended behaviour for a schema extension.

`TemplateId` is unchanged (E3 identity controls own it); bounds change a facet, not the id.

## 2. `reverse_reference_coordinator_v1.spl` additions (owner module)

```simple
pub struct AffectedConsumerV1:
    consumer: SemanticQueryKeyV1
    partition_id: text

pub struct AffectedConsumersV1:
    accepted: bool
    rejection_reason: text
    affected: [AffectedConsumerV1]   # sorted by canonical consumer, then partition; unique

pub struct GenericInvalidationPlanV1:
    accepted: bool
    rejection_reason: text
    changed_facets: [text]           # sorted unique facet names
    affected: [AffectedConsumerV1]
    affected_partitions: [text]      # sorted unique

pub fn generic_changed_semantic_facets_v1(template: SemanticQueryKeyV1,
        changes: [GenericFacetChangeV1]) -> [ChangedSemanticFacetV1]
pub fn affected_consumers_v1(changed_facets, old_new_membership,
        verified_forward_manifests, rr_shards) -> AffectedConsumersV1
pub fn plan_generic_invalidation_v1(template: SemanticQueryKeyV1,
        changes: [GenericFacetChangeV1], verified_forward_manifests, rr_shards)
        -> GenericInvalidationPlanV1
```

`affected_consumers_v1` runs exactly the validation of `_plan_affected_queries_authenticated_v1`
up to (not including) the authority gate, with the same rejection strings
(`affected_domain_bounds_exceeded` for the row/byte preflight, `invalid_changed_facet`,
`invalid_changed_fingerprint`, `membership_or_absence_incomplete`,
`forward_manifest_unverified`, `rr_shard_incomplete` — checked per shard right after the
row bound so a corrupt edge digest is reported as the shard defect it is —
`affected_evidence_incomplete`, `affected_domain_incomplete`), then computes the `(consumer, partition)` pairs from RR edges
and verified forward reads matched on `(producer, facet)`. It is the exactness seam: no SCC
expansion, no authority. It is pure and reads no disk.

Empty `changed_facets` with valid evidence -> accepted, `affected == []` (unrelated edit).
`plan_generic_invalidation_v1` maps the facet changes (`dimension = "generic"`), rejects a
change whose facet is not one of the three generic facets (`invalid_changed_facet`), and
delegates to `affected_consumers_v1`.

The authenticated planner (`plan_affected_queries_with_authority_v1`) is unchanged; it
now shares the pair computation through a private helper `_affected_pairs_v1`.

## 3. New `80.driver/driver_build/hir_variant_object_key_v1.spl`

```simple
pub val HIR_VARIANT_PROJECTION_SCHEMA_V1 = "hir-variant-projection/v1"
pub val HIR_VARIANT_OBJECT_KEY_SCHEMA_V1 = "hir-variant-object/v1"

pub struct HirCfgDeclV1:
    name: text
    kind: text               # fn|struct|class|enum|trait|const|impl
    cfg: [text]
    cfg_group: i64
    cfg_arm: i64
    content_digest: text     # 64-hex sha256 of the decl's target-neutral HIR

pub struct HirVariantProjectionV1:
    ok: bool
    error: text
    target_id: text
    kept: [text]             # "<kind>:<name>" in declaration order
    variant_digest: text     # "" when not ok

pub fn hir_variant_target_id_v1(target: MirTargetContext) -> text
    # "<arch>[.<subarch>]-<os>-<abi>-<backend>/<build_profile>/<cpu_tier or 'baseline'>"
    # subarch is included because @cfg atoms (thumb, armv7, ...) select on it
pub fn hir_variant_projection_v1(decls: [HirCfgDeclV1], target: MirTargetContext,
        features: [text]) -> HirVariantProjectionV1
pub fn hir_variant_object_key_v1(module_path: text, projection: HirVariantProjectionV1,
        toolchain_identity: text) -> text          # "" when projection.ok is false or inputs empty
pub fn hir_variant_object_partition_v1(base_partition: text,
        projection: HirVariantProjectionV1) -> text   # base + "@" + target_id; "" when not ok
pub fn hir_variant_object_producer_v1(module_path: text, profile_digest: text,
        projection: HirVariantProjectionV1) -> SemanticQueryKeyV1
    # kind "obj.emit" (a known semantic query kind), stable_entity_id module_path,
    # semantic_profile_digest profile_digest, parameter_digest variant_digest
pub fn hir_variant_object_sidecar_path_v1(queue: text, module_name: text, target_id: text) -> text
    # target_id == "" -> "<queue>/<sha256(module)>.object" (legacy, byte-identical)
    # otherwise      -> "<queue>/<sha256(module + "\u0000" + target_id)>.object"
```

Projection algorithm (mirrors `MirLowering.cfg_group_winners` + `decl_cfg_keep`):

1. Validate every decl: non-empty name, known kind, 64-hex `content_digest`; otherwise
   `ok=false, error="invalid_decl"`.
2. For each `cfg_group != 0`: collect distinct arms ordered by `cfg_arm` with `-1` (else)
   last; condition = `cfg.join(" and ")`, `""` for the else arm; a numbered arm with empty
   cfg or `cfg_arm < -1` -> `error="malformed_cfg_group"`; `mir_cfg_select_arm == -2` ->
   `error="malformed_cfg"`; winner = selected arm or -99.
3. A decl is kept iff (`cfg_group == 0` and `mir_cfg_item_enabled == 1`) or
   (`cfg_group != 0` and `cfg_arm == winner`); `mir_cfg_item_enabled == -2` -> `error="malformed_cfg"`.
4. `variant_digest = sha256(frame(schema) + frame(target_id) + frame(kept.len()) + for kept: frame(kind) + frame(name) + frame(content_digest))`.

Object key: `sha256(frame(schema) + frame(module_path) + frame(variant_digest) + frame(target_id) + frame(toolchain_identity))`.

## 4. `native_file_worker_v1.spl` facade (additive, trailing)

```simple
pub fn native_file_worker_object_path_for_target_v1(queue: text, module_name: text,
        target_id: text) -> text
```
Reads the sidecar at `hir_variant_object_sidecar_path_v1(queue, module_name, target_id)`;
with `target_id == ""` it is byte-for-byte `native_file_worker_object_path_v1`.

## 5. Error handling summary

| Input | Result |
|---|---|
| corrupt RR shard bytes | `reverse_reference_shard_decode_v1.ok == false`; `read_reverse_reference_shard_v1` -> `rr_shard_decode_rejected`; plan never built |
| shard coverage Unknown | `rr_shard_incomplete` |
| corrupt generic section | `generic_template_section_decode_v1.ok == false`, `error` names the frame |
| facet name outside the three | `invalid_changed_facet` |
| malformed `@cfg` | projection `ok=false`; key, partition, producer parameter are `""` |
| empty module path / toolchain | key `""` |

## 6. Compile-safety notes (no self-hosted binary on this host)

- Only trailing defaulted struct fields are added (seed fills positionally).
- No `nil` outside `Option` match arms; no `Any`.
- New module imports only `std.common.crypto.sha256`, `compiler.common.mir_target_context`,
  `compiler.mir.mir_cfg_select`, `compiler.common.cache_contract.semantic_query_read_manifest_v1`,
  `compiler.common.cache_contract.physical_tld_v1`.
