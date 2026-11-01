# Exact generic reverse-reference invalidation (lane generic-rr-hir-variant-obj)

> Drives `affected_consumers_v1` and `plan_generic_invalidation_v1` over an in-memory fixture: template producer T, its template object O (edges on all three generic facets), callers C1/C2 (signature + bound only), a dependent D of C1, and an unrelated consumer U. Over- and under-invalidation are both asserted, plus every rejection string and canonical ordering/dedup. A second partition (windows variant) proves per-variant isolation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Exact generic reverse-reference invalidation (lane generic-rr-hir-variant-obj)

Drives `affected_consumers_v1` and `plan_generic_invalidation_v1` over an in-memory fixture: template producer T, its template object O (edges on all three generic facets), callers C1/C2 (signature + bound only), a dependent D of C1, and an unrelated consumer U. Over- and under-invalidation are both asserted, plus every rejection string and canonical ordering/dedup. A second partition (windows variant) proves per-variant isolation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Requirements | doc/03_plan/sys_test/generic_rr_hir_variant_obj.md (REQ-GRR-001..009) |
| Plan | doc/03_plan/sys_test/generic_rr_hir_variant_obj.md |
| Design | doc/05_design/generic_rr_hir_variant_obj.md |
| Research | doc/01_research/local/generic_rr_hir_variant_obj.md |
| Source | `test/01_unit/compiler/cache/generic_rr_exact_invalidation_spec.spl` |
| Updated | 2026-11-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Drives `affected_consumers_v1` and `plan_generic_invalidation_v1` over an
in-memory fixture: template producer T, its template object O (edges on all
three generic facets), callers C1/C2 (signature + bound only), a dependent D
of C1, and an unrelated consumer U. Over- and under-invalidation are both
asserted, plus every rejection string and canonical ordering/dedup. A second
partition (windows variant) proves per-variant isolation.

Evidence: Rust-seed interpreter runs only (attributed to the seed); no self-hosted
binary exists on the authoring host. Owner: reverse_reference_coordinator_v1.spl.

## Scenarios

### generic RR exact invalidation: per-facet consumer sets

#### body change affects only the template object O (REQ-GRR-001)

- Plan a generic.body change on T and expect exactly [O] (REQ-GRR-001)
   - Expected: plan.accepted is true
   - Expected: plan.changed_facets equals `[GENERIC_FACET_BODY_V1]`
   - Expected: plan.affected.len() equals `1`
   - Expected: ids(plan.affected) equals `["pkg_a.Pair#object"]`
   - Expected: ids(plan.affected) does not contain `pkg_b.C1`
   - Expected: ids(plan.affected) does not contain `pkg_b.C2`
   - Expected: ids(plan.affected) does not contain `pkg_z.U`
   - Expected: plan.affected_partitions equals `[LINUX_PART]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a generic.body change on T and expect exactly [O] (REQ-GRR-001)")
val plan = plan_t([GENERIC_FACET_BODY_V1])
expect(plan.accepted).to_equal(true)
expect(plan.changed_facets).to_equal([GENERIC_FACET_BODY_V1])
expect(plan.affected.len()).to_equal(1)
expect(ids(plan.affected)).to_equal(["pkg_a.Pair#object"])
expect(ids(plan.affected).contains("pkg_b.C1")).to_equal(false)
expect(ids(plan.affected).contains("pkg_b.C2")).to_equal(false)
expect(ids(plan.affected).contains("pkg_z.U")).to_equal(false)
expect(plan.affected_partitions).to_equal([LINUX_PART])
```

</details>

#### signature change affects O, C1 and C2 but not U (REQ-GRR-002)

- Plan a generic.signature change on T (REQ-GRR-002)
   - Expected: plan.accepted is true
   - Expected: plan.affected.len() equals `3`
   - Expected: ids(plan.affected) contains `pkg_a.Pair#object`
   - Expected: ids(plan.affected) contains `pkg_b.C1`
   - Expected: ids(plan.affected) contains `pkg_b.C2`
   - Expected: ids(plan.affected) does not contain `pkg_z.U`
   - Expected: ids(plan.affected) does not contain `pkg_c.D`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a generic.signature change on T (REQ-GRR-002)")
val plan = plan_t([GENERIC_FACET_SIGNATURE_V1])
expect(plan.accepted).to_equal(true)
expect(plan.affected.len()).to_equal(3)
expect(ids(plan.affected).contains("pkg_a.Pair#object")).to_equal(true)
expect(ids(plan.affected).contains("pkg_b.C1")).to_equal(true)
expect(ids(plan.affected).contains("pkg_b.C2")).to_equal(true)
expect(ids(plan.affected).contains("pkg_z.U")).to_equal(false)
expect(ids(plan.affected).contains("pkg_c.D")).to_equal(false)
```

</details>

#### bound change affects O, C1 and C2 but not U (REQ-GRR-003)

- Plan a generic.bound change on T (REQ-GRR-003)
   - Expected: plan.accepted is true
   - Expected: plan.changed_facets equals `[GENERIC_FACET_BOUND_V1]`
   - Expected: plan.affected.len() equals `3`
   - Expected: ids(plan.affected) contains `pkg_a.Pair#object`
   - Expected: ids(plan.affected) contains `pkg_b.C1`
   - Expected: ids(plan.affected) contains `pkg_b.C2`
   - Expected: ids(plan.affected) does not contain `pkg_z.U`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a generic.bound change on T (REQ-GRR-003)")
val plan = plan_t([GENERIC_FACET_BOUND_V1])
expect(plan.accepted).to_equal(true)
expect(plan.changed_facets).to_equal([GENERIC_FACET_BOUND_V1])
# Exact set: three distinct ids present and the length is three.
expect(plan.affected.len()).to_equal(3)
expect(ids(plan.affected).contains("pkg_a.Pair#object")).to_equal(true)
expect(ids(plan.affected).contains("pkg_b.C1")).to_equal(true)
expect(ids(plan.affected).contains("pkg_b.C2")).to_equal(true)
expect(ids(plan.affected).contains("pkg_z.U")).to_equal(false)
```

</details>

#### caller edit affects only the caller's dependents (REQ-GRR-004)

- Change generic.signature on producer C1 and expect only D (REQ-GRR-004)
   - Expected: result.accepted is true
   - Expected: ids(result.affected) equals `["pkg_c.D"]`
   - Expected: ids(result.affected) does not contain `pkg_a.Pair#object`
   - Expected: ids(result.affected) does not contain `pkg_b.C2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Change generic.signature on producer C1 and expect only D (REQ-GRR-004)")
val result = affected_consumers_v1([change(caller("pkg_b.C1"), GENERIC_FACET_SIGNATURE_V1)], [],
    verified_all(linux_manifests()), shards_of(linux_manifests()))
expect(result.accepted).to_equal(true)
expect(ids(result.affected)).to_equal(["pkg_c.D"])
expect(ids(result.affected).contains("pkg_a.Pair#object")).to_equal(false)
expect(ids(result.affected).contains("pkg_b.C2")).to_equal(false)
```

</details>

#### no changes is accepted with an empty affected set (REQ-GRR-006)

- Plan with zero generic facet changes (REQ-GRR-006)
   - Expected: plan.accepted is true
   - Expected: plan.rejection_reason equals ``
   - Expected: plan.affected.len() equals `0`
   - Expected: plan.affected_partitions.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan with zero generic facet changes (REQ-GRR-006)")
val plan = plan_t([])
expect(plan.accepted).to_equal(true)
expect(plan.rejection_reason).to_equal("")
expect(plan.affected.len()).to_equal(0)
expect(plan.affected_partitions.len()).to_equal(0)
```

</details>

#### a change on the linux variant does not affect the windows partition (REQ-GRR-005)

- Change the linux variant producer and expect only the linux user (REQ-GRR-005)
   - Expected: result.accepted is true
   - Expected: ids(result.affected) equals `["app-linux"]`
   - Expected: result.affected[0].partition_id equals `LINUX_PART`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Change the linux variant producer and expect only the linux user (REQ-GRR-005)")
val ms = variant_manifests()
val result = affected_consumers_v1([change(linux_variant(), GENERIC_FACET_BODY_V1)], [],
    verified_all(ms), shards_of(ms))
expect(result.accepted).to_equal(true)
expect(ids(result.affected)).to_equal(["app-linux"])
expect(result.affected[0].partition_id).to_equal(LINUX_PART)
```

</details>

### generic RR exact invalidation: canonical output

#### orders affected consumers canonically and de-duplicates RR and forward hits

- Plan a signature+bound change where O is reached by edges and forward reads
   - Expected: plan.accepted is true
   - Expected: plan.changed_facets equals `[GENERIC_FACET_BOUND_V1, GENERIC_FACET_SIGNATURE_V1]`
   - Expected: plan.affected.len() equals `3`
   - Expected: a0 < a1 is true
   - Expected: a1 < a2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a signature+bound change where O is reached by edges and forward reads")
val plan = plan_t([GENERIC_FACET_SIGNATURE_V1, GENERIC_FACET_BOUND_V1, GENERIC_FACET_SIGNATURE_V1])
expect(plan.accepted).to_equal(true)
expect(plan.changed_facets).to_equal([GENERIC_FACET_BOUND_V1, GENERIC_FACET_SIGNATURE_V1])
expect(plan.affected.len()).to_equal(3)
val a0 = semantic_query_key_canonical_v1(plan.affected[0].consumer)
val a1 = semantic_query_key_canonical_v1(plan.affected[1].consumer)
val a2 = semantic_query_key_canonical_v1(plan.affected[2].consumer)
expect(a0 < a1).to_equal(true)
expect(a1 < a2).to_equal(true)
```

</details>

#### maps generic facet changes onto the generic dimension

- Map a body change for T into ChangedSemanticFacetV1 rows
   - Expected: rows.len() equals `1`
   - Expected: rows[0].dimension equals `GENERIC_FACET_DIMENSION_V1`
   - Expected: rows[0].facet equals `GENERIC_FACET_BODY_V1`
   - Expected: rows[0].producer equals `template_t()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Map a body change for T into ChangedSemanticFacetV1 rows")
val rows = generic_changed_semantic_facets_v1(template_t(), [gchange(GENERIC_FACET_BODY_V1)])
expect(rows.len()).to_equal(1)
expect(rows[0].dimension).to_equal(GENERIC_FACET_DIMENSION_V1)
expect(rows[0].facet).to_equal(GENERIC_FACET_BODY_V1)
expect(rows[0].producer).to_equal(template_t())
```

</details>

### generic RR exact invalidation: fail-closed rejections

#### rejects a facet name outside the three generic facets

- Plan a change whose facet is generic.layout
   - Expected: plan.accepted is false
   - Expected: plan.rejection_reason equals `invalid_changed_facet`
   - Expected: plan.affected.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a change whose facet is generic.layout")
val plan = plan_t(["generic.layout"])
expect(plan.accepted).to_equal(false)
expect(plan.rejection_reason).to_equal("invalid_changed_facet")
expect(plan.affected.len()).to_equal(0)
```

</details>

#### rejects a shard with Unknown coverage

- Downgrade one shard to Unknown coverage and plan a body change
   - Expected: plan.accepted is false
   - Expected: plan.rejection_reason equals `rr_shard_incomplete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Downgrade one shard to Unknown coverage and plan a body change")
val shards = shards_of(linux_manifests())
val s = shards[0]
val unknown = ReverseReferenceShardV1(schema: s.schema, partition_id: s.partition_id,
    coverage: SemanticCoverageV1.Unknown, sorted_edges: s.sorted_edges)
val plan = plan_generic_invalidation_v1(template_t(), [gchange(GENERIC_FACET_BODY_V1)],
    verified_all(linux_manifests()), [unknown])
expect(plan.accepted).to_equal(false)
expect(plan.rejection_reason).to_equal("rr_shard_incomplete")
```

</details>

#### rejects changes without verified forward manifests

- Plan a body change with no forward manifests
   - Expected: plan.accepted is false
   - Expected: plan.rejection_reason equals `affected_evidence_incomplete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a body change with no forward manifests")
val plan = plan_generic_invalidation_v1(template_t(), [gchange(GENERIC_FACET_BODY_V1)],
    [], shards_of(linux_manifests()))
expect(plan.accepted).to_equal(false)
expect(plan.rejection_reason).to_equal("affected_evidence_incomplete")
```

</details>

#### rejects a tampered forward manifest digest

- Replace O's manifest digest with an unrelated digest
   - Expected: result.accepted is false
   - Expected: result.rejection_reason equals `forward_manifest_unverified`
   - Expected: result.affected.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Replace O's manifest digest with an unrelated digest")
val good = verified_all(linux_manifests())
val v = good[0]
val tampered = VerifiedForwardManifestV1(manifest_digest: digest("tampered"),
    manifest: v.manifest, scc_group: v.scc_group, affected_domains: v.affected_domains)
val result = affected_consumers_v1([change(template_t(), GENERIC_FACET_BODY_V1)], [],
    [tampered], shards_of(linux_manifests()))
expect(result.accepted).to_equal(false)
expect(result.rejection_reason).to_equal("forward_manifest_unverified")
expect(result.affected.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/03_plan/sys_test/generic_rr_hir_variant_obj.md (REQ-GRR-001..009)`
- **Plan:** `doc/03_plan/sys_test/generic_rr_hir_variant_obj.md`
- **Design:** `doc/05_design/generic_rr_hir_variant_obj.md`
- **Research:** `doc/01_research/local/generic_rr_hir_variant_obj.md`


</details>
