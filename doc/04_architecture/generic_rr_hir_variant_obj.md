# Architecture: generic reverse references and per-target objects from HIR variants

Lane `generic-rr-hir-variant-obj`. Research: `doc/01_research/local/generic_rr_hir_variant_obj.md`.
Detail design: `doc/05_design/generic_rr_hir_variant_obj.md`.
Plan: `doc/03_plan/compiler/generics/generics_refactoring_formal_verification_plan_2026-10-31.md` 1A, 8.

## 1. Modules (MDSOC: one authority per concern, facades kept)

```
00.common/cache_contract/generic_tldr_view_v1.spl      (owner: generic facets + fingerprints)
        |  GenericFacetChangeV1[]
        v
80.driver/cache/reference/reverse_reference_coordinator_v1.spl
        |  (owner: ChangedSemanticFacetV1 mapping, exact affected set, generic plan)
        |
80.driver/driver_build/hir_variant_object_key_v1.spl   (NEW owner: variant projection,
        |                                               per-target object key, partition, sidecar path)
        v
80.driver/driver_build/native_file_worker_v1.spl       (facade: object path per target; additive)
```

Dependencies point downward only. `hir_variant_object_key_v1` depends on
`compiler.common.mir_target_context` and `compiler.mir.mir_cfg_select` (pure evaluators) and
never on `MirLowering`. The coordinator does not import the driver_build module; the variant
reaches RR as data (`partition_id`, `parameter_digest`).

## 2. Facet model for generics (erased model, one body)

| Facet | Fingerprint source | Consumed by |
|---|---|---|
| `generic.signature` | symbol_id, params (kind, binder_id), fields (name, type_key) — `generic_template_summary_digest_v1` | every type-arg-bearing caller; the template's own object action |
| `generic.bound` | bounds sorted by (param_index, bound_key) | every type-arg-bearing caller; the template's own object action |
| `generic.body` | `body_digest` of the single erased body | the template's own object action only |

Dimension for all three: `generic`. A caller never records a `generic.body` read: under
the erased model it links one body symbol and does not embed it. Hence:

- body edit -> changed facets = {body} -> affected = template object action(s) only;
- signature or bound edit -> affected = every caller with that edge (+ template object);
- caller edit -> the caller's own producer fingerprint changes; its consumers are
  affected, the template is not (no edge from template to caller exists);
- unrelated edit (same facets) -> zero changed facets -> empty affected set, accepted.

Exactness is a set equality: affected == { consumer | exists RR edge or verified forward
read (producer = template, facet in changed) }. No SCC expansion is applied in the pure
seam; the authenticated planner keeps its SCC expansion for mixed-epoch safety.

## 3. Variant dimension

HIR stays target-neutral. For a target `T` the **variant projection** is the ordered list of
decls that `MirLowering.decl_cfg_keep` would keep, computed by the same pure evaluators
(`mir_cfg_item_enabled`, `mir_cfg_select_arm`, else arm last, malformed = fail closed).

```
variant_digest(T) = sha256( "hir-variant-projection/v1", target_id(T),
                            for kept decl in declaration order: (kind, name, content_digest) )
object_key(M, T)  = sha256( "hir-variant-object/v1", module_path, variant_digest(T),
                            target_id(T), toolchain_identity )
partition(M, T)   = base_partition + "@" + target_id(T)
producer(M, T)    = SemanticQueryKeyV1(kind "object", stable_entity_id module_path,
                                       parameter_digest variant_digest(T))
```

A decl that target `T` drops is not in `variant_digest(T)`; editing it changes only the
variants that keep it, so only those objects (and the RR partitions of those targets) are
invalidated. The whole-module HIR digest is excluded from the key on purpose.

## 4. Pipeline placement (one process per file)

```
parse -> HIR (all arms) -> [for each requested target T]
                              projection(T) -> object_key(M,T) -> hit? reuse : MIR(T) -> .o(T)
```

The unit process already does parse -> HIR -> MIR -> obj. Adding targets multiplies only the
MIR+obj stage; projection and key computation are O(decls) and happen before MIR so the
first object (first target) is not delayed. NFR: first `.o` within 10 s of unit start
(measured by `hir_start_ms` -> `obj_done_ms` in `NativeFileWorkerReceiptV1`).

The MIR ledger sidecar becomes `<queue>/<sha256(module + "\0" + target_id)>.object`; with
`target_id == ""` the legacy path is returned unchanged, so the current bootstrap lane is
not disturbed until the worker switches targets on.

## 5. Failure policy (plan 8.2, 8.6)

- Corrupt RR shard, corrupt generic section, invalid fingerprint, unverified forward
  manifest, `Unknown`/`Conservative` coverage -> plan rejected with the existing reason
  strings; never an empty-success.
- Malformed `@cfg` guard -> projection `ok = false`, object key `""`, no sidecar path.
- Concurrent rebuild: two writers stage from the same prior generation; staging is pure
  and deterministic, so the staged shard sets are equal and the atomic generation owner
  (`reverse_reference_atomic_generation_v2`) decides the single committed generation.
  Replaying the same delta is idempotent (`rr_delta_insert_edge_conflict` only on a
  conflicting fingerprint).

## 6. Out of scope (recorded gaps)

- Turning the worker on for multiple targets per unit (needs the self-hosted binary and
  the phase-3 lane's agreement); this lane lands the key/partition/path owner and the
  additive facade.
- Projecting bounds and body digests from source in `generic_tldr_projector.spl`
  (`GenericDeclInputV1` gains optional `bounds`/`body_digest` inputs only).
- Writer-grant authority for RR publication (`affected_query_domain_authority_available_v1`
  stays false).
