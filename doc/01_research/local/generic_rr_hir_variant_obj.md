# Local research: generic reverse references + object files from HIR variants

Lane: `generic-rr-hir-variant-obj` (2026-11-01, base `origin/release/1.0.0@8a935437a98`).
Plan context: `doc/03_plan/compiler/generics/generics_refactoring_formal_verification_plan_2026-10-31.md`
sections 1A (execution status) and 8 (TLDR, reverse references, SCV, incremental reuse).

Everything below was established by reading the release tree; nothing was built or run.
No self-hosted `bin/release/<triple>/simple` exists on this Windows host (same gap as
plan row E3), so every spec in this lane is authored UNRUN until a binary is announced.

## 1. Owners that already exist

| Concern | Owner on release | What it already does |
|---|---|---|
| Generic template identity | `src/compiler/00.common/cache_contract/generic_tldr_view_v1.spl` | `GenericTemplateEntryV1` (symbol_id, source_digest, visibility_root, active_guard_root, language_schema, binder-indexed params, fields); `generic_template_summary_digest_v1` (params + fields, display names excluded); `generic_template_id_v1` (tagged SHA-256 over summary + visibility + guard + schema); `generic_args_id_v1`; `concrete_tldr_key_v1`; strict indexed-section codec that fails closed. |
| Template projection from source | `src/compiler/10.frontend/cache_artifact/generic_tldr_projector.spl` | `GenericDeclInputV1 -> GenericTemplateEntryV1`; no bounds, no body digest are projected today. |
| Reverse-reference scheduling | `src/compiler/80.driver/cache/reference/reverse_reference_coordinator_v1.spl` | `ChangedSemanticFacetV1` (producer query, facet, dimension, old/new fingerprint); `plan_affected_queries_v1` matches RR edges and verified forward reads by `(producer, facet)` and expands through the SCC witness; `stage_reverse_delta_v1` / `stage_reverse_shards_v1` / `seed_reverse_shards_v1` (genesis distinct from update, missing history rejected); `persist_/read_reverse_reference_shard_v1` through the verified CAS (decode failure -> `rr_shard_decode_rejected`). |
| RR edge/shard codec | `src/compiler/00.common/cache_contract/reverse_reference_shard_v1.spl` | `ReverseReferenceEdgeV1 {producer, facet, consumer, consumed_fingerprint, forward_manifest_digest, partition_id}`; shards are per `partition_id`, sorted, coverage-tagged; strict decode. |
| Forward read manifests | `src/compiler/00.common/cache_contract/semantic_query_read_manifest_v1.spl` | `SemanticQueryKeyV1 {kind, stable_entity_id, semantic_profile_digest, parameter_digest}`; `SemanticQueryReadV1` with `facet`, `partition_id`, `completeness`. |
| Atomic RR generation | `src/compiler/80.driver/cache/reference/reverse_reference_atomic_generation_v2.spl` | `prepare_rr_atomic_generation_v2`, `recover_rr_atomic_generation_v2`; publisher authority still reports unavailable (`rr_atomic_generation_publisher_authority_available_v2() == false`). |
| Target-neutral HIR | `src/compiler/20.hir/hir_definitions.spl` | Every decl (`HirFunction`, `HirClass`, `HirStruct`, `HirEnum`, `HirTrait`, `HirConst`, `HirImpl`) carries `cfg: [text]`, `cfg_group: i64`, `cfg_arm: i64`; HIR keeps every arm. |
| Target selection in MIR | `src/compiler/50.mir/mir_cfg_select.spl`, `50.mir/_MirLowering/asm_and_targets.spl` | `mir_cfg_item_enabled` (standalone guard), `mir_cfg_select_arm` (grouped arms, else last, -2 malformed), `MirLowering.decl_cfg_keep` / `cfg_group_winners` pick one arm per group for `MirTargetContext`. Reads no environment. |
| HIR cache key | `src/compiler/80.driver/driver_hir_cache.spl` | `hir_cache_key` folds `native_target` plus a strip-decision digest unless the file and its closure are proven target-neutral (`hir-target-neutral-v1`). |
| Per-file pipeline | `src/compiler/80.driver/driver_build/native_file_worker_v1.spl`, `native_mir_shard.spl` | One unit process per file (parse -> HIR -> MIR -> object); the MIR ledger records one `.object` sidecar per module at `<queue>/<sha256(module)>.object` — **one object per module, no target dimension**. |
| Config variant key (packages) | `src/compiler/80.driver/cache/package_tldr_metadata.spl` | `ConfigVariantKeyV1 {target_triple, backend, features, build_mode, language_abi, normalized_options, environment_inputs}` — package-level precedent for a variant-bearing key. |

## 2. Gaps found

1. **No generic facets.** The RR coordinator matches by free-form `facet` text; nothing defines
   which facets a generic template exposes. A template edit therefore cannot be classified as
   body / signature / bound, so a consumer either over-invalidates (any edit) or is not
   recorded at all.
2. **No bounds, no body digest in the template entry.** `GenericTemplateEntryV1` stores params
   and fields only. A bound edit is invisible to the TLDR view; a body edit is only visible
   through `source_digest`, which also changes on an unrelated edit in the same file.
3. **Object keys ignore the target.** The per-file MIR ledger keys its `.object` sidecar by
   module name only. Building two targets from one target-neutral HIR would overwrite one
   object with the other, and an edit inside a `@cfg(os = "windows")` arm would invalidate
   the Linux object too (the HIR cache key folds the whole file).
4. **Variant selection is only reachable through `MirLowering` methods** (`decl_cfg_keep`,
   `cfg_group_winners`) that need a live lowering context; no pure function returns "which
   decls survive for target T" so a cache key can be derived before lowering.
5. **Authority gate hides the exact set.** `plan_affected_queries_v1` returns
   `affected_domain_authority_unavailable` before computing the affected pairs when no writer
   grant exists (see `reverse_reference_empty_and_multi_scc_spec.spl`). A pure "exact affected
   consumers" seam is needed to test exactness (no over-/under-invalidation) without a grant.

## 3. Concurrent work (read only)

- E0 `work/generics-erased-body-land-20261101` (`C:/dev/wt/e0-erased-body`, not merged at
  base): erased execution model; touches `native_file_worker_v1.spl` (2 lines). This lane adds
  only trailing functions to that file to keep a rebase trivial. Generics are one erased body:
  a caller never consumes the body facet, only signature + bound.
- E3 `generic-tldr-identity-controls` (merged as #5720 at base): extended
  `test/01_unit/compiler/cache/generic_tldr_view_v1_spec.spl`; this lane does not rewrite it.

## 4. Decisions carried into the design

- Reuse `ChangedSemanticFacetV1` / `plan_affected_queries_v1` / `stage_reverse_shards_v1` as
  the one RR authority (plan 8.1, 8.4); add generic facet names and a pure exact-set seam
  rather than a second index.
- Keep `TemplateId` unchanged (E3 owns identity controls); bounds and body become **facets**
  with their own fingerprints.
- The target dimension enters RR through the `partition_id` and the producer's
  `parameter_digest` (= variant projection digest), not through a new edge field.
- Object key = `(module path, variant projection digest, target id, toolchain identity)`; the
  whole-module HIR digest is deliberately NOT in the key, so an edit to an arm that target T
  drops leaves T's key unchanged.
