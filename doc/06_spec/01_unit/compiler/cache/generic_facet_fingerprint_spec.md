# Generic template facet fingerprints (lane generic-rr-hir-variant-obj)

> A generic template entry exposes three reverse-reference facets: `generic.signature`, `generic.bound` and `generic.body`. This unit spec checks the fingerprint laws (alpha invariance, bound order/duplicate insensitivity, body tracking), the changed-facet diff for body, signature, bound and unrelated edits, the caller/template consumed facet sets, and the fail-closed section codec for bounds and body_digest.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic template facet fingerprints (lane generic-rr-hir-variant-obj)

A generic template entry exposes three reverse-reference facets: `generic.signature`, `generic.bound` and `generic.body`. This unit spec checks the fingerprint laws (alpha invariance, bound order/duplicate insensitivity, body tracking), the changed-facet diff for body, signature, bound and unrelated edits, the caller/template consumed facet sets, and the fail-closed section codec for bounds and body_digest.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Requirements | doc/03_plan/sys_test/generic_rr_hir_variant_obj.md (REQ-GRR-001..009) |
| Plan | doc/03_plan/sys_test/generic_rr_hir_variant_obj.md |
| Design | doc/05_design/generic_rr_hir_variant_obj.md |
| Research | doc/01_research/local/generic_rr_hir_variant_obj.md |
| Source | `test/01_unit/compiler/cache/generic_facet_fingerprint_spec.spl` |
| Updated | 2026-11-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

A generic template entry exposes three reverse-reference facets:
`generic.signature`, `generic.bound` and `generic.body`. This unit spec
checks the fingerprint laws (alpha invariance, bound order/duplicate
insensitivity, body tracking), the changed-facet diff for body, signature,
bound and unrelated edits, the caller/template consumed facet sets, and the
fail-closed section codec for bounds and body_digest.

Evidence: Rust-seed interpreter runs only (attributed to the seed); no self-hosted
binary exists on the authoring host. Owner: generic_tldr_view_v1.spl.

## Scenarios

### generic facet fingerprints

#### signature fingerprint changes with a field type and is alpha-invariant (REQ-GRR-002)

- Compare signature fingerprints for retyped and binder-renamed Pair (REQ-GRR-002)
   - Expected: generic_template_signature_fingerprint_v1(pair_entry_retyped()) == a is false
   - Expected: generic_template_signature_fingerprint_v1(pair_entry_renamed()) equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare signature fingerprints for retyped and binder-renamed Pair (REQ-GRR-002)")
val a = generic_template_signature_fingerprint_v1(pair_entry())
expect(generic_template_signature_fingerprint_v1(pair_entry_retyped()) == a).to_equal(false)
expect(generic_template_signature_fingerprint_v1(pair_entry_renamed())).to_equal(a)
```

</details>

#### bound fingerprint is order and duplicate insensitive (REQ-GRR-003)

- Fingerprint the same bound set in two orders with a duplicate (REQ-GRR-003)
   - Expected: generic_template_bound_fingerprint_v1(one) equals `generic_template_bound_fingerprint_v1(two)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fingerprint the same bound set in two orders with a duplicate (REQ-GRR-003)")
val e = pair_entry()
val one = with_facets(e, [bound(1, "trait:pkg_a.Ord"), bound(0, "trait:pkg_a.Eq")], "")
val two = with_facets(e, [bound(0, "trait:pkg_a.Eq"), bound(1, "trait:pkg_a.Ord"),
    bound(0, "trait:pkg_a.Eq")], "")
expect(generic_template_bound_fingerprint_v1(one)).to_equal(generic_template_bound_fingerprint_v1(two))
```

</details>

#### bound fingerprint differs between no bound and one bound (REQ-GRR-003)

- Compare the no-bound and one-bound fingerprints (REQ-GRR-003)
   - Expected: none_fp.len() equals `64`
   - Expected: none_fp == one_fp is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare the no-bound and one-bound fingerprints (REQ-GRR-003)")
val none_fp = generic_template_bound_fingerprint_v1(with_facets(pair_entry(), [], ""))
val one_fp = generic_template_bound_fingerprint_v1(with_facets(pair_entry(), [bound(0, "trait:pkg_a.Eq")], ""))
expect(none_fp.len()).to_equal(64)
expect(none_fp == one_fp).to_equal(false)
```

</details>

#### body fingerprint tracks body_digest (REQ-GRR-001)

- Fingerprint two body digests and the same digest twice (REQ-GRR-001)
   - Expected: v1 == v2 is false
   - Expected: generic_template_body_fingerprint_v1(with_facets(pair_entry(), [], digest("body-v1"))) equals `v1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fingerprint two body digests and the same digest twice (REQ-GRR-001)")
val v1 = generic_template_body_fingerprint_v1(with_facets(pair_entry(), [], digest("body-v1")))
val v2 = generic_template_body_fingerprint_v1(with_facets(pair_entry(), [], digest("body-v2")))
expect(v1 == v2).to_equal(false)
expect(generic_template_body_fingerprint_v1(with_facets(pair_entry(), [], digest("body-v1")))).to_equal(v1)
```

</details>

#### generic_template_facets_v1 returns three 64-hex fingerprints

- Project the facets of a bounded Pair with a body
   - Expected: f.template_id equals `generic_template_id_v1(base())`
   - Expected: three_payload_contract_digest_valid_v1(f.signature_fingerprint) is true
   - Expected: three_payload_contract_digest_valid_v1(f.bound_fingerprint) is true
   - Expected: three_payload_contract_digest_valid_v1(f.body_fingerprint) is true
   - Expected: f.signature_fingerprint == f.body_fingerprint is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project the facets of a bounded Pair with a body")
val f = generic_template_facets_v1(base())
expect(f.template_id).to_equal(generic_template_id_v1(base()))
expect(three_payload_contract_digest_valid_v1(f.signature_fingerprint)).to_equal(true)
expect(three_payload_contract_digest_valid_v1(f.bound_fingerprint)).to_equal(true)
expect(three_payload_contract_digest_valid_v1(f.body_fingerprint)).to_equal(true)
expect(f.signature_fingerprint == f.body_fingerprint).to_equal(false)
```

</details>

### generic changed-facet diff

#### body-only edit yields exactly generic.body (REQ-GRR-001)

- Diff a template whose only change is body_digest (REQ-GRR-001)
   - Expected: facet_names(changes) equals `[GENERIC_FACET_BODY_V1]`
   - Expected: is_none_text(changes[0].old_fingerprint) is false
   - Expected: is_none_text(changes[0].new_fingerprint) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Diff a template whose only change is body_digest (REQ-GRR-001)")
val changes = generic_template_changed_facets_v1(Some(base()),
    Some(with_facets(pair_entry(), [bound(0, "trait:pkg_a.Eq")], digest("body-v2"))))
expect(facet_names(changes)).to_equal([GENERIC_FACET_BODY_V1])
expect(is_none_text(changes[0].old_fingerprint)).to_equal(false)
expect(is_none_text(changes[0].new_fingerprint)).to_equal(false)
```

</details>

#### signature edit yields exactly generic.signature (REQ-GRR-002)

- Diff a template whose field type changed (REQ-GRR-002)
   - Expected: facet_names(changes) equals `[GENERIC_FACET_SIGNATURE_V1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Diff a template whose field type changed (REQ-GRR-002)")
val changes = generic_template_changed_facets_v1(Some(base()),
    Some(with_facets(pair_entry_retyped(), [bound(0, "trait:pkg_a.Eq")], digest("body-v1"))))
expect(facet_names(changes)).to_equal([GENERIC_FACET_SIGNATURE_V1])
```

</details>

#### bound edit yields exactly generic.bound (REQ-GRR-003)

- Diff a template whose bound key changed (REQ-GRR-003)
   - Expected: facet_names(changes) equals `[GENERIC_FACET_BOUND_V1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Diff a template whose bound key changed (REQ-GRR-003)")
val changes = generic_template_changed_facets_v1(Some(base()),
    Some(with_facets(pair_entry(), [bound(0, "trait:pkg_a.Ord")], digest("body-v1"))))
expect(facet_names(changes)).to_equal([GENERIC_FACET_BOUND_V1])
```

</details>

#### unrelated edit changing only source_digest yields no facets (REQ-GRR-006)

- Diff identical semantics with a different source_digest (REQ-GRR-006)
   - Expected: changes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Diff identical semantics with a different source_digest (REQ-GRR-006)")
val changes = generic_template_changed_facets_v1(Some(base()),
    Some(with_source(base(), "src:pkg_a.Pair:edited-comment")))
expect(changes.len()).to_equal(0)
```

</details>

#### genesis yields three changes with nil old fingerprints

- Diff nil against a new template
   - Expected: facet_names(changes) equals `[GENERIC_FACET_BODY_V1, GENERIC_FACET_BOUND_V1,`
   - Expected: is_none_text(c.old_fingerprint) is true
   - Expected: is_none_text(c.new_fingerprint) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Diff nil against a new template")
val changes = generic_template_changed_facets_v1(nil, Some(base()))
expect(facet_names(changes)).to_equal([GENERIC_FACET_BODY_V1, GENERIC_FACET_BOUND_V1,
    GENERIC_FACET_SIGNATURE_V1])
for c in changes:
    expect(is_none_text(c.old_fingerprint)).to_equal(true)
    expect(is_none_text(c.new_fingerprint)).to_equal(false)
```

</details>

#### removal yields three changes with nil new fingerprints

- Diff an existing template against nil
   - Expected: changes.len() equals `3`
   - Expected: is_none_text(c.old_fingerprint) is false
   - Expected: is_none_text(c.new_fingerprint) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Diff an existing template against nil")
val changes = generic_template_changed_facets_v1(Some(base()), nil)
expect(changes.len()).to_equal(3)
for c in changes:
    expect(is_none_text(c.old_fingerprint)).to_equal(false)
    expect(is_none_text(c.new_fingerprint)).to_equal(true)
```

</details>

#### nil to nil yields no changes

- Diff nil against nil
   - Expected: generic_template_changed_facets_v1(nil, nil).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Diff nil against nil")
expect(generic_template_changed_facets_v1(nil, nil).len()).to_equal(0)
```

</details>

### generic consumed facet sets

#### callers consume signature and bound but never body (REQ-GRR-001)

- Read the caller consumed facet set (REQ-GRR-001)
   - Expected: facets equals `[GENERIC_FACET_BOUND_V1, GENERIC_FACET_SIGNATURE_V1]`
   - Expected: facets does not contain `GENERIC_FACET_BODY_V1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the caller consumed facet set (REQ-GRR-001)")
val facets = generic_caller_consumed_facets_v1()
expect(facets).to_equal([GENERIC_FACET_BOUND_V1, GENERIC_FACET_SIGNATURE_V1])
expect(facets.contains(GENERIC_FACET_BODY_V1)).to_equal(false)
```

</details>

#### the template object consumes body, bound and signature

- Read the template consumed facet set
   - Expected: facets equals `[GENERIC_FACET_BODY_V1, GENERIC_FACET_BOUND_V1,`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read the template consumed facet set")
val facets = generic_template_consumed_facets_v1()
expect(facets).to_equal([GENERIC_FACET_BODY_V1, GENERIC_FACET_BOUND_V1,
    GENERIC_FACET_SIGNATURE_V1])
```

</details>

### generic section codec with bounds and body (REQ-GRR-008)

#### round-trips bounds and body_digest

- Encode and decode a section carrying bounds and a body digest (REQ-GRR-008)
   - Expected: d.ok is true
   - Expected: d.section.digest equals `s.digest`
   - Expected: d.section.entries[0].bounds.len() equals `2`
   - Expected: d.section.entries[0].bounds[1].bound_key equals `trait:pkg_a.Ord`
   - Expected: d.section.entries[0].body_digest equals `digest("body-v1")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Encode and decode a section carrying bounds and a body digest (REQ-GRR-008)")
val s = build_generic_template_section_v1([with_facets(pair_entry(),
    [bound(0, "trait:pkg_a.Eq"), bound(1, "trait:pkg_a.Ord")], digest("body-v1"))])
val d = generic_template_section_decode_v1(generic_template_section_encode_v1(s))
expect(d.ok).to_equal(true)
expect(d.section.digest).to_equal(s.digest)
expect(d.section.entries[0].bounds.len()).to_equal(2)
expect(d.section.entries[0].bounds[1].bound_key).to_equal("trait:pkg_a.Ord")
expect(d.section.entries[0].body_digest).to_equal(digest("body-v1"))
```

</details>

#### fails closed on an out-of-range bound index

- Decode a section whose bound index exceeds the parameter count (REQ-GRR-008)
   - Expected: s.entries.len() equals `1`
   - Expected: d.ok is false
   - Expected: d.error equals `bad bound`
   - Expected: d.section.entries.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Decode a section whose bound index exceeds the parameter count (REQ-GRR-008)")
val s = build_generic_template_section_v1([with_facets(pair_entry(),
    [bound(9, "trait:pkg_a.Eq")], digest("body-v1"))])
# The builder seals whatever it is given; the strict decoder is the gate.
expect(s.entries.len()).to_equal(1)
val d = generic_template_section_decode_v1(generic_template_section_encode_v1(s))
expect(d.ok).to_equal(false)
expect(d.error).to_equal("bad bound")
expect(d.section.entries.len()).to_equal(0)
```

</details>

#### fails closed when the encoded body digest is corrupted

- Corrupt the body digest frame and decode (REQ-GRR-008)
   - Expected: generic_template_section_decode_v1(encoded).ok is true
   - Expected: bad == encoded is false
   - Expected: generic_template_section_decode_v1(bad).ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Corrupt the body digest frame and decode (REQ-GRR-008)")
val s = build_generic_template_section_v1([base()])
val encoded = generic_template_section_encode_v1(s)
expect(generic_template_section_decode_v1(encoded).ok).to_equal(true)
val bad = encoded.replace(digest("body-v1"), digest("body-xx"))
expect(bad == encoded).to_equal(false)
expect(generic_template_section_decode_v1(bad).ok).to_equal(false)
```

</details>

#### generic_bounds_valid_v1 rejects an out-of-range index and an empty key

- Validate in-range, out-of-range and empty-key bounds
   - Expected: generic_bounds_valid_v1(with_facets(pair_entry(), [bound(1, "trait:pkg_a.Eq")], "")) is true
   - Expected: generic_bounds_valid_v1(with_facets(pair_entry(), [bound(2, "trait:pkg_a.Eq")], "")) is false
   - Expected: generic_bounds_valid_v1(with_facets(pair_entry(), [bound(-1, "trait:pkg_a.Eq")], "")) is false
   - Expected: generic_bounds_valid_v1(with_facets(pair_entry(), [bound(0, "")], "")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Validate in-range, out-of-range and empty-key bounds")
expect(generic_bounds_valid_v1(with_facets(pair_entry(), [bound(1, "trait:pkg_a.Eq")], ""))).to_equal(true)
expect(generic_bounds_valid_v1(with_facets(pair_entry(), [bound(2, "trait:pkg_a.Eq")], ""))).to_equal(false)
expect(generic_bounds_valid_v1(with_facets(pair_entry(), [bound(-1, "trait:pkg_a.Eq")], ""))).to_equal(false)
expect(generic_bounds_valid_v1(with_facets(pair_entry(), [bound(0, "")], ""))).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/03_plan/sys_test/generic_rr_hir_variant_obj.md (REQ-GRR-001..009)`
- **Plan:** `doc/03_plan/sys_test/generic_rr_hir_variant_obj.md`
- **Design:** `doc/05_design/generic_rr_hir_variant_obj.md`
- **Research:** `doc/01_research/local/generic_rr_hir_variant_obj.md`


</details>
