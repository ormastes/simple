# Generic RR exactness and HIR-variant objects (system)

> End-to-end over the public owners only: one target-neutral `HirCfgDeclV1`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic RR exactness and HIR-variant objects (system)

End-to-end over the public owners only: one target-neutral `HirCfgDeclV1`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Requirements | doc/03_plan/sys_test/generic_rr_hir_variant_obj.md (REQ-GRR-001..009) |
| Plan | doc/03_plan/sys_test/generic_rr_hir_variant_obj.md |
| Design | doc/05_design/generic_rr_hir_variant_obj.md |
| Research | doc/01_research/local/generic_rr_hir_variant_obj.md |
| Source | `test/03_system/compiler/feature/generic_rr_hir_variant_obj_spec.spl` |
| Updated | 2026-11-01 |
| Generator | `simple spipe-docgen` (Simple) |

End-to-end over the public owners only: one target-neutral `HirCfgDeclV1`
list projected for linux and windows yields per-target object keys, RR
partitions and RR producers; generic template edits flow through facet
diffing, forward manifests, rebuilt RR shards and the generic invalidation
plan. Each scenario (body, signature, bound, caller, cfg-variant, unrelated,
concurrent rebuild, cache corruption, two keys per module) asserts the full
chain.

UNRUN on the self-hosted binary: none is available on the authoring host.
NFR-GRR-001 (first object within 10 s) is a live worker measurement and is
deliberately not asserted here; see the test plan for its command.

## Scenarios

### system: generic body edit

#### invalidates only the template object across both partitions (REQ-GRR-001)

- Edit the Pair body and plan over the two-target shard set (REQ-GRR-001)
   - Expected: plan.accepted is true
   - Expected: plan.changed_facets equals `[GENERIC_FACET_BODY_V1]`
   - Expected: ids(plan.affected) equals `["pkg_a.Pair#object"]`
   - Expected: plan.affected_partitions equals `[part(linux())]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Edit the Pair body and plan over the two-target shard set (REQ-GRR-001)")
val plan = plan_edit(entry("Second", "trait:pkg_a.Eq", "body-v2"))
expect(plan.accepted).to_equal(true)
expect(plan.changed_facets).to_equal([GENERIC_FACET_BODY_V1])
expect(ids(plan.affected)).to_equal(["pkg_a.Pair#object"])
expect(plan.affected_partitions).to_equal([part(linux())])
```

</details>

### system: generic signature edit

#### invalidates the template object and every caller only (REQ-GRR-002)

- Retype a Pair field and plan (REQ-GRR-002)
   - Expected: plan.accepted is true
   - Expected: plan.affected.len() equals `3`
   - Expected: ids(plan.affected) contains `pkg_b.C1`
   - Expected: ids(plan.affected) contains `pkg_b.C2`
   - Expected: ids(plan.affected) does not contain `pkg_c.D`
   - Expected: ids(plan.affected) does not contain `app-windows`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Retype a Pair field and plan (REQ-GRR-002)")
val plan = plan_edit(entry("i64", "trait:pkg_a.Eq", "body-v1"))
expect(plan.accepted).to_equal(true)
expect(plan.affected.len()).to_equal(3)
expect(ids(plan.affected).contains("pkg_b.C1")).to_equal(true)
expect(ids(plan.affected).contains("pkg_b.C2")).to_equal(true)
expect(ids(plan.affected).contains("pkg_c.D")).to_equal(false)
expect(ids(plan.affected).contains("app-windows")).to_equal(false)
```

</details>

### system: generic bound edit

#### invalidates the template object and every caller only (REQ-GRR-003)

- Change the Pair bound and plan (REQ-GRR-003)
   - Expected: plan.accepted is true
   - Expected: plan.changed_facets equals `[GENERIC_FACET_BOUND_V1]`
   - Expected: plan.affected.len() equals `3`
   - Expected: ids(plan.affected) contains `pkg_a.Pair#object`
   - Expected: ids(plan.affected) contains `pkg_b.C1`
   - Expected: ids(plan.affected) contains `pkg_b.C2`
   - Expected: ids(plan.affected) does not contain `pkg_c.D`
   - Expected: ids(plan.affected) does not contain `app-linux`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Change the Pair bound and plan (REQ-GRR-003)")
val plan = plan_edit(entry("Second", "trait:pkg_a.Ord", "body-v1"))
expect(plan.accepted).to_equal(true)
expect(plan.changed_facets).to_equal([GENERIC_FACET_BOUND_V1])
expect(plan.affected.len()).to_equal(3)
expect(ids(plan.affected).contains("pkg_a.Pair#object")).to_equal(true)
expect(ids(plan.affected).contains("pkg_b.C1")).to_equal(true)
expect(ids(plan.affected).contains("pkg_b.C2")).to_equal(true)
expect(ids(plan.affected).contains("pkg_c.D")).to_equal(false)
expect(ids(plan.affected).contains("app-linux")).to_equal(false)
```

</details>

### system: caller edit

#### restages only C1 and invalidates only C1's dependent (REQ-GRR-004)

- Restage C1 with a new type-argument read and plan a C1 change (REQ-GRR-004)
   - Expected: staged.accepted is true
   - Expected: result.accepted is true
   - Expected: ids(result.affected) equals `["pkg_c.D"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Restage C1 with a new type-argument read and plan a C1 change (REQ-GRR-004)")
val staged = stage_reverse_shards_v1(shards(), Some(c1_old()), c1_new(), true)
expect(staged.accepted).to_equal(true)
val result = affected_consumers_v1([change(key("tldr.concrete", "pkg_b.C1"),
    GENERIC_FACET_SIGNATURE_V1, digest("c1-sig"), digest("c1-sig-v2"))], [], verified_all(), staged.shards)
expect(result.accepted).to_equal(true)
expect(ids(result.affected)).to_equal(["pkg_c.D"])
```

</details>

### system: cfg-variant edit

#### moves the windows key and partition only (REQ-GRR-005)

- Edit the windows-only decl and compare keys and affected partitions (REQ-GRR-005)
   - Expected: kl_new equals `kl_old`
   - Expected: kw_new == kw_old is false
   - Expected: result.accepted is true
   - Expected: ids(result.affected) equals `["app-windows"]`
   - Expected: result.affected[0].partition_id equals `part(windows())`
   - Expected: result.affected[0].partition_id == part(linux()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Edit the windows-only decl and compare keys and affected partitions (REQ-GRR-005)")
val kl_old = hir_variant_object_key_v1(MODULE, projection(linux(), "w-v1"), TOOLCHAIN)
val kl_new = hir_variant_object_key_v1(MODULE, projection(linux(), "w-v2"), TOOLCHAIN)
val kw_old = hir_variant_object_key_v1(MODULE, projection(windows(), "w-v1"), TOOLCHAIN)
val kw_new = hir_variant_object_key_v1(MODULE, projection(windows(), "w-v2"), TOOLCHAIN)
expect(kl_new).to_equal(kl_old)
expect(kw_new == kw_old).to_equal(false)
val pw_old = projection(windows(), "w-v1")
val pw_new = projection(windows(), "w-v2")
val result = affected_consumers_v1([change(hir_variant_object_producer_v1(MODULE, digest("profile"), pw_old),
    GENERIC_FACET_BODY_V1, pw_old.variant_digest, pw_new.variant_digest)], [], verified_all(), shards())
expect(result.accepted).to_equal(true)
expect(ids(result.affected)).to_equal(["app-windows"])
expect(result.affected[0].partition_id).to_equal(part(windows()))
expect(result.affected[0].partition_id == part(linux())).to_equal(false)
```

</details>

### system: unrelated edit

#### yields no changed facets and an accepted empty plan (REQ-GRR-006)

- Plan a comment-only edit that moves the source digest but no facet (REQ-GRR-006)
   - Expected: new_e.source_digest == old_entry().source_digest is false
   - Expected: plan.accepted is true
   - Expected: plan.changed_facets.len() equals `0`
   - Expected: plan.affected.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Plan a comment-only edit that moves the source digest but no facet (REQ-GRR-006)")
val new_e = unrelated_entry()
expect(new_e.source_digest == old_entry().source_digest).to_equal(false)
val plan = plan_edit(new_e)
expect(plan.accepted).to_equal(true)
expect(plan.changed_facets.len()).to_equal(0)
expect(plan.affected.len()).to_equal(0)
```

</details>

### system: concurrent rebuild

#### stages identical canonical shards from the same prior and replays idempotently (REQ-GRR-007)

- Stage the C1 edit twice concurrently from one prior, then replay (REQ-GRR-007)
   - Expected: a.accepted is true
   - Expected: encode_all(a.shards) equals `encode_all(b.shards)`
   - Expected: a.shards.len() equals `2`
   - Expected: encode_all(replay.shards) equals `encode_all(a.shards)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Stage the C1 edit twice concurrently from one prior, then replay (REQ-GRR-007)")
val prior = shards()
val a = stage_reverse_shards_v1(prior, Some(c1_old()), c1_new(), true)
val b = stage_reverse_shards_v1(prior, Some(c1_old()), c1_new(), true)
expect(a.accepted).to_equal(true)
expect(encode_all(a.shards)).to_equal(encode_all(b.shards))
expect(a.shards.len()).to_equal(2)
val replay = stage_reverse_shards_v1(a.shards, Some(c1_new()), c1_new(), true)
expect(encode_all(replay.shards)).to_equal(encode_all(a.shards))
```

</details>

### system: cache corruption

#### fails closed on corrupt shard bytes and a corrupt generic section (REQ-GRR-008)

- Flip a shard byte and corrupt a generic section, then decode both (REQ-GRR-008)
   - Expected: reverse_reference_shard_decode_v1(bytes).ok is true
   - Expected: reverse_reference_shard_decode_v1(bad).ok is false
   - Expected: generic_template_section_decode_v1(corrupt).ok is false
   - Expected: generic_template_section_decode_v1(section).ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Flip a shard byte and corrupt a generic section, then decode both (REQ-GRR-008)")
val bytes = reverse_reference_shard_encode_v1(shards()[0])
# Positive control first: the uncorrupted bytes decode, so the negative
# result below is the corruption and not a vacuous decoder failure.
expect(reverse_reference_shard_decode_v1(bytes).ok).to_equal(true)
var bad = bytes
if bytes[0] == 0:
    bad[0] = 1
else:
    bad[0] = 0
expect(reverse_reference_shard_decode_v1(bad).ok).to_equal(false)
val section = generic_template_section_encode_v1(build_generic_template_section_v1([old_entry()]))
val corrupt = section.replace(digest("body-v1"), digest("body-zz"))
expect(generic_template_section_decode_v1(corrupt).ok).to_equal(false)
expect(generic_template_section_decode_v1(section).ok).to_equal(true)
```

</details>

### system: one HIR, one object key per target

#### derives two distinct deterministic keys for one module (REQ-GRR-009)

- Key the module for linux and windows from the same HIR, twice (REQ-GRR-009)
   - Expected: kl.len() equals `64`
   - Expected: kw.len() equals `64`
   - Expected: kl == kw is false
   - Expected: hir_variant_object_key_v1(MODULE, projection(linux(), "w-v1"), TOOLCHAIN) equals `kl`
   - Expected: hir_variant_object_key_v1(MODULE, projection(windows(), "w-v1"), TOOLCHAIN) equals `kw`
   - Expected: part(linux()) == part(windows()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Key the module for linux and windows from the same HIR, twice (REQ-GRR-009)")
val kl = hir_variant_object_key_v1(MODULE, projection(linux(), "w-v1"), TOOLCHAIN)
val kw = hir_variant_object_key_v1(MODULE, projection(windows(), "w-v1"), TOOLCHAIN)
expect(kl.len()).to_equal(64)
expect(kw.len()).to_equal(64)
expect(kl == kw).to_equal(false)
expect(hir_variant_object_key_v1(MODULE, projection(linux(), "w-v1"), TOOLCHAIN)).to_equal(kl)
expect(hir_variant_object_key_v1(MODULE, projection(windows(), "w-v1"), TOOLCHAIN)).to_equal(kw)
expect(part(linux()) == part(windows())).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/03_plan/sys_test/generic_rr_hir_variant_obj.md (REQ-GRR-001..009)`
- **Plan:** `doc/03_plan/sys_test/generic_rr_hir_variant_obj.md`
- **Design:** `doc/05_design/generic_rr_hir_variant_obj.md`
- **Research:** `doc/01_research/local/generic_rr_hir_variant_obj.md`


</details>
