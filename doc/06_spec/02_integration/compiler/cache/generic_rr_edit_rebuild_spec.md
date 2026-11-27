# Generic RR edit -> rebuild loop (lane generic-rr-hir-variant-obj)

> In-memory end-to-end loop: old/new `GenericTemplateEntryV1` -> `generic_template_changed_facets_v1` -> `generic_changed_semantic_facets_v1` -> forward manifests (reads named by the generic facet constants, consumed fingerprints taken from `generic_template_facets_v1`) -> `rebuild_reverse_shards_from_forward_v1` -> `plan_generic_invalidation_v1`. Covers body, signature, bound, caller, cfg-variant and unrelated edits, the concurrent rebuild / replay law and RR cache corruption.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic RR edit -> rebuild loop (lane generic-rr-hir-variant-obj)

In-memory end-to-end loop: old/new `GenericTemplateEntryV1` -> `generic_template_changed_facets_v1` -> `generic_changed_semantic_facets_v1` -> forward manifests (reads named by the generic facet constants, consumed fingerprints taken from `generic_template_facets_v1`) -> `rebuild_reverse_shards_from_forward_v1` -> `plan_generic_invalidation_v1`. Covers body, signature, bound, caller, cfg-variant and unrelated edits, the concurrent rebuild / replay law and RR cache corruption.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Requirements | doc/03_plan/sys_test/generic_rr_hir_variant_obj.md (REQ-GRR-001..009) |
| Plan | doc/03_plan/sys_test/generic_rr_hir_variant_obj.md |
| Design | doc/05_design/generic_rr_hir_variant_obj.md |
| Research | doc/01_research/local/generic_rr_hir_variant_obj.md |
| Source | `test/02_integration/compiler/cache/generic_rr_edit_rebuild_spec.spl` |
| Updated | 2026-11-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

In-memory end-to-end loop: old/new `GenericTemplateEntryV1` ->
`generic_template_changed_facets_v1` -> `generic_changed_semantic_facets_v1`
-> forward manifests (reads named by the generic facet constants, consumed
fingerprints taken from `generic_template_facets_v1`) ->
`rebuild_reverse_shards_from_forward_v1` -> `plan_generic_invalidation_v1`.
Covers body, signature, bound, caller, cfg-variant and unrelated edits, the
concurrent rebuild / replay law and RR cache corruption.

Evidence: Rust-seed interpreter runs only (attributed to the seed; the positive RRS1
decode control is seed-RED because the seed misreads the envelope). No disk is
touched; persistence is covered by the coordinator's own specs.

## Scenarios

### generic RR edit-rebuild loop: template edits

#### rebuilds shards from the forward manifests

- Rebuild reverse shards from the four forward manifests
   - Expected: staged.accepted is true
   - Expected: staged.shards.len() equals `1`
   - Expected: staged.shards[0].partition_id equals `p@x86_64-linux-gnu-llvm/debug/baseline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Rebuild reverse shards from the four forward manifests")
val staged = rebuild_reverse_shards_from_forward_v1(manifests())
expect(staged.accepted).to_equal(true)
expect(staged.shards.len()).to_equal(1)
expect(staged.shards[0].partition_id).to_equal("p@x86_64-linux-gnu-llvm/debug/baseline")
```

</details>

#### body edit invalidates only the template object (REQ-GRR-001)

- Edit the body digest and plan the invalidation (REQ-GRR-001)
   - Expected: rows.len() equals `1`
   - Expected: rows[0].facet equals `GENERIC_FACET_BODY_V1`
   - Expected: plan.accepted is true
   - Expected: ids(plan.affected) equals `["pkg_a.Pair#object"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Edit the body digest and plan the invalidation (REQ-GRR-001)")
val changes = generic_template_changed_facets_v1(Some(old_entry()),
    Some(entry("Second", "trait:pkg_a.Eq", "body-v2")))
val rows = generic_changed_semantic_facets_v1(template_t(), changes)
expect(rows.len()).to_equal(1)
expect(rows[0].facet).to_equal(GENERIC_FACET_BODY_V1)
val plan = plan_edit(entry("Second", "trait:pkg_a.Eq", "body-v2"))
expect(plan.accepted).to_equal(true)
expect(ids(plan.affected)).to_equal(["pkg_a.Pair#object"])
```

</details>

#### signature edit invalidates the template object and both callers (REQ-GRR-002)

- Retype a field and plan the invalidation (REQ-GRR-002)
   - Expected: plan.accepted is true
   - Expected: plan.changed_facets equals `[GENERIC_FACET_SIGNATURE_V1]`
   - Expected: plan.affected.len() equals `3`
   - Expected: ids(plan.affected) does not contain `pkg_c.D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Retype a field and plan the invalidation (REQ-GRR-002)")
val plan = plan_edit(entry("i64", "trait:pkg_a.Eq", "body-v1"))
expect(plan.accepted).to_equal(true)
expect(plan.changed_facets).to_equal([GENERIC_FACET_SIGNATURE_V1])
expect(plan.affected.len()).to_equal(3)
expect(ids(plan.affected).contains("pkg_c.D")).to_equal(false)
```

</details>

#### bound edit invalidates the template object and both callers (REQ-GRR-003)

- Change the bound key and plan the invalidation (REQ-GRR-003)
   - Expected: plan.accepted is true
   - Expected: plan.changed_facets equals `[GENERIC_FACET_BOUND_V1]`
   - Expected: plan.affected.len() equals `3`
   - Expected: ids(plan.affected) contains `pkg_b.C1`
   - Expected: ids(plan.affected) contains `pkg_b.C2`
   - Expected: ids(plan.affected) contains `pkg_a.Pair#object`
   - Expected: ids(plan.affected) does not contain `pkg_c.D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Change the bound key and plan the invalidation (REQ-GRR-003)")
val plan = plan_edit(entry("Second", "trait:pkg_a.Ord", "body-v1"))
expect(plan.accepted).to_equal(true)
expect(plan.changed_facets).to_equal([GENERIC_FACET_BOUND_V1])
expect(plan.affected.len()).to_equal(3)
expect(ids(plan.affected).contains("pkg_b.C1")).to_equal(true)
expect(ids(plan.affected).contains("pkg_b.C2")).to_equal(true)
expect(ids(plan.affected).contains("pkg_a.Pair#object")).to_equal(true)
expect(ids(plan.affected).contains("pkg_c.D")).to_equal(false)
```

</details>

#### unrelated edit yields an accepted empty plan (REQ-GRR-006)

- Re-plan after a comment-only edit that changes only the source digest (REQ-GRR-006)
   - Expected: plan.accepted is true
   - Expected: plan.changed_facets.len() equals `0`
   - Expected: plan.affected.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Re-plan after a comment-only edit that changes only the source digest (REQ-GRR-006)")
val plan = plan_edit(unrelated_entry())
expect(plan.accepted).to_equal(true)
expect(plan.changed_facets.len()).to_equal(0)
expect(plan.affected.len()).to_equal(0)
```

</details>

### generic RR edit-rebuild loop: caller and cfg-variant edits

#### caller edit stages a delta only for C1 and invalidates only its dependent (REQ-GRR-004)

- Stage C1's old to new manifest delta and plan a C1 signature change (REQ-GRR-004)
   - Expected: delta.consumer equals `caller("pkg_b.C1")`
   - Expected: delta.inserted.len() equals `3`
   - Expected: delta.removed.len() equals `2`
   - Expected: e.consumer equals `caller("pkg_b.C1")`
   - Expected: e.forward_manifest_digest equals `delta.new_manifest_digest`
   - Expected: inserted_producers contains `tldr.concrete`
   - Expected: e.consumer equals `caller("pkg_b.C1")`
   - Expected: e.producer equals `template_t()`
   - Expected: result.accepted is true
   - Expected: ids(result.affected) equals `["pkg_c.D"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Stage C1's old to new manifest delta and plan a C1 signature change (REQ-GRR-004)")
val delta = stage_reverse_delta_v1(Some(c1_old()), c1_new())
expect(delta.consumer).to_equal(caller("pkg_b.C1"))
# Edges are bound to their forward-manifest digest (plan 8.4), so C1's
# new manifest re-keys all three of its edges and retires the two old
# ones; no edge of any other consumer moves.
expect(delta.inserted.len()).to_equal(3)
expect(delta.removed.len()).to_equal(2)
var inserted_producers: [text] = []
for e in delta.inserted:
    expect(e.consumer).to_equal(caller("pkg_b.C1"))
    expect(e.forward_manifest_digest).to_equal(delta.new_manifest_digest)
    inserted_producers = inserted_producers.push(e.producer.kind)
expect(inserted_producers.contains("tldr.concrete")).to_equal(true)
for e in delta.removed:
    expect(e.consumer).to_equal(caller("pkg_b.C1"))
    expect(e.producer).to_equal(template_t())
val result = affected_consumers_v1([ChangedSemanticFacetV1(producer: caller("pkg_b.C1"),
    facet: GENERIC_FACET_SIGNATURE_V1, dimension: GENERIC_FACET_DIMENSION_V1,
    old_fingerprint: Some(digest("c1-signature-v1")), new_fingerprint: Some(digest("c1-signature-v2")))],
    [], verified_all(manifests()), shards())
expect(result.accepted).to_equal(true)
expect(ids(result.affected)).to_equal(["pkg_c.D"])
```

</details>

#### cfg-variant edit affects only the windows partition (REQ-GRR-005)

- Edit the windows-only decl and plan against linux and windows partitions (REQ-GRR-005)
   - Expected: pl_new.variant_digest equals `pl.variant_digest`
   - Expected: pw_new.variant_digest == pw_old.variant_digest is false
   - Expected: result.accepted is true
   - Expected: ids(result.affected) equals `["app-windows"]`
   - Expected: result.affected[0].partition_id equals `part_w`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Edit the windows-only decl and plan against linux and windows partitions (REQ-GRR-005)")
val pl = hir_variant_projection_v1(cfg_decls("w-v1"), linux(), [])
val pw_old = hir_variant_projection_v1(cfg_decls("w-v1"), windows(), [])
val pw_new = hir_variant_projection_v1(cfg_decls("w-v2"), windows(), [])
val pl_new = hir_variant_projection_v1(cfg_decls("w-v2"), linux(), [])
expect(pl_new.variant_digest).to_equal(pl.variant_digest)
expect(pw_new.variant_digest == pw_old.variant_digest).to_equal(false)
val part_l = hir_variant_object_partition_v1(BASE_PART, pl)
val part_w = hir_variant_object_partition_v1(BASE_PART, pw_old)
val prod_l = hir_variant_object_producer_v1("pkg_v.main", digest("profile"), pl)
val prod_w = hir_variant_object_producer_v1("pkg_v.main", digest("profile"), pw_old)
val ms = [manifest(key("obj.link", "app-linux"), [read_at(prod_l, key("obj.link", "app-linux"),
        GENERIC_FACET_BODY_V1, digest("obj-l"), 0, part_l)]),
    manifest(key("obj.link", "app-windows"), [read_at(prod_w, key("obj.link", "app-windows"),
        GENERIC_FACET_BODY_V1, digest("obj-w"), 0, part_w)])]
val result = affected_consumers_v1([ChangedSemanticFacetV1(producer: prod_w,
    facet: GENERIC_FACET_BODY_V1, dimension: GENERIC_FACET_DIMENSION_V1,
    old_fingerprint: Some(pw_old.variant_digest), new_fingerprint: Some(pw_new.variant_digest))],
    [], verified_all(ms), rebuild_reverse_shards_from_forward_v1(ms).shards)
expect(result.accepted).to_equal(true)
expect(ids(result.affected)).to_equal(["app-windows"])
expect(result.affected[0].partition_id).to_equal(part_w)
```

</details>

### generic RR edit-rebuild loop: concurrency and corruption

#### two concurrent rebuilds from the same prior stage identical shards and replay is idempotent (REQ-GRR-007)

- Stage C1's delta twice from the same prior and replay it once more (REQ-GRR-007)
   - Expected: first.accepted is true
   - Expected: second.accepted is true
   - Expected: encode_all(first.shards) equals `encode_all(second.shards)`
   - Expected: replay.accepted is true
   - Expected: encode_all(replay.shards) equals `encode_all(first.shards)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Stage C1's delta twice from the same prior and replay it once more (REQ-GRR-007)")
val prior = shards()
val first = stage_reverse_shards_v1(prior, Some(c1_old()), c1_new(), true)
val second = stage_reverse_shards_v1(prior, Some(c1_old()), c1_new(), true)
expect(first.accepted).to_equal(true)
expect(second.accepted).to_equal(true)
expect(encode_all(first.shards)).to_equal(encode_all(second.shards))
val replay = stage_reverse_shards_v1(first.shards, Some(c1_new()), c1_new(), true)
expect(replay.accepted).to_equal(true)
expect(encode_all(replay.shards)).to_equal(encode_all(first.shards))
```

</details>

#### a flipped shard byte fails decode closed (REQ-GRR-008)

- Flip the first byte of an encoded shard and decode it (REQ-GRR-008)
   - Expected: reverse_reference_shard_decode_v1(bytes).ok is true
   - Expected: reverse_reference_shard_decode_v1(bad).ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Flip the first byte of an encoded shard and decode it (REQ-GRR-008)")
val bytes = reverse_reference_shard_encode_v1(shards()[0])
expect(reverse_reference_shard_decode_v1(bytes).ok).to_equal(true)
var bad = bytes
if bytes[0] == 0:
    bad[0] = 1
else:
    bad[0] = 0
expect(reverse_reference_shard_decode_v1(bad).ok).to_equal(false)
```

</details>

#### a shard edge with an invalid consumed fingerprint rejects the plan (REQ-GRR-008)

- Plan a body edit against a shard whose edge fingerprint is zz (REQ-GRR-008)
   - Expected: plan.accepted is false
   - Expected: plan.rejection_reason equals `rr_shard_incomplete`
   - Expected: plan.affected.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a body edit against a shard whose edge fingerprint is zz (REQ-GRR-008)")
val good = shards()[0].sorted_edges[0]
val corrupt = ReverseReferenceShardV1(schema: 1, partition_id: good.partition_id,
    coverage: SemanticCoverageV1.Complete,
    sorted_edges: [ReverseReferenceEdgeV1(producer: good.producer, facet: good.facet,
        consumer: good.consumer, consumed_fingerprint: "zz",
        forward_manifest_digest: good.forward_manifest_digest, partition_id: good.partition_id)])
val changes = generic_template_changed_facets_v1(Some(old_entry()),
    Some(entry("Second", "trait:pkg_a.Eq", "body-v2")))
val plan = plan_generic_invalidation_v1(template_t(), changes, verified_all(manifests()), [corrupt])
expect(plan.accepted).to_equal(false)
expect(plan.rejection_reason).to_equal("rr_shard_incomplete")
expect(plan.affected.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/03_plan/sys_test/generic_rr_hir_variant_obj.md (REQ-GRR-001..009)`
- **Plan:** `doc/03_plan/sys_test/generic_rr_hir_variant_obj.md`
- **Design:** `doc/05_design/generic_rr_hir_variant_obj.md`
- **Research:** `doc/01_research/local/generic_rr_hir_variant_obj.md`


</details>
