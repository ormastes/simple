# Generic template section v3 (`generic_template_section_v3`)

> Purpose: pin the behaviour of the section schema that carries each generic

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Generic template section v3 (`generic_template_section_v3`)

Purpose: pin the behaviour of the section schema that carries each generic

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Plan | doc/03_plan/language/type_system/no_any_inference_plan.md (rows S3-F0..F10, row S3-F1) |
| Design | doc/05_design/compiler/cache/generic_instance_tldr_trace.md (sections 3, 4, 5, 9, 14) |
| Research | doc/01_research/compiler/compile_speed/mono_instance_census_2026-10-19.md (instance census this stage serves) |
| Source | `test/01_unit/compiler/cache/generic_template_section_v3_spec.spl` |
| Updated | 2026-11-28 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: pin the behaviour of the section schema that carries each generic
template's open needs next to the unchanged v2 template table: the set-once
fill, the sealed v3 encoding, its strict decoding, and the plan's acceptance
sentence for stage S3-F1: editing a body so that it needs one more instance
changes the decoded open needs and the keys of that template's instances; a
binder rename changes neither; a v2 reader misses.

Audience: compiler-cache maintainers and reviewers of incremental rebuilds,
who must know that open needs can never move a template identity, and that a
reader of the wrong schema misses instead of guessing.

Scope: `src/compiler/00.common/cache_contract/generic_template_section_v3.spl`,
exercised together with the v1/v2 section codecs and the template identity
functions of `generic_tldr_view_v1.spl` (not re-specified here).

Assumptions: an instance key is built as in the S3-F1 design, by folding the
identity digest of the template's open needs into the concrete key.

Limitations: the evidence is runs of this spec on the Rust-seed interpreter
(`simple-local-20261128f.exe`); no native-compiled run backs it. Tampered wires
are re-sealed by hand with the layout documented in the module header.

Verification and troubleshooting: run `simple test` on this file and read the
`SPEC FILE VERDICT:` line. A failing refusal scenario means the decoder's error
wording or its rule order changed; both are part of the contract.

**Research:** doc/01_research/compiler/compile_speed/mono_instance_census_2026-10-19.md (instance census this stage serves)
**Architecture:** doc/04_architecture/generic_rr_hir_variant_obj.md (generic template facets and instance objects)
**Plan:** doc/03_plan/language/type_system/no_any_inference_plan.md (rows S3-F0..F10, row S3-F1)
**Design:** doc/05_design/compiler/cache/generic_instance_tldr_trace.md (sections 3, 4, 5, 9, 14)

| Requirement | Plan acceptance sentence it serves |
|---|---|
| REQ-GENERIC-F1B-001 set-once fill | the slot is filled once by the typed-HIR stage |
| REQ-GENERIC-F1B-002 body edit | editing a body so that it needs one more instance changes the decoded open needs and the keys of that template's instances |
| REQ-GENERIC-F1B-003 binder rename | a binder rename changes neither |
| REQ-GENERIC-F1B-004 identity untouched | open needs sit in no template id and no facet fingerprint |
| REQ-GENERIC-F1B-005 reader misses | a v2 reader misses; a v3 reader refuses v2 and v1 |
| REQ-GENERIC-F1B-006 strict decode | every malformed v3 wire is refused with its own reason |

## Scenarios

### template section v3 with open needs (plan S3-F1)

#### Filling the open-needs slot of a template

#### a fresh template

#### has an absent slot after projection

- produce the slot state of a freshly projected template
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: slot_is_absent(box_template()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("produce the slot state of a freshly projected template")
# @req REQ-GENERIC-F1B-001
expect(slot_is_absent(box_template())).to_equal(true)
```

</details>

#### the first fill

#### stores the canonical form of the rows

- project a template and fill it with rows given out of order
   - Exec capture: after_step
- read the stored rows back
   - Expected: stored.len() equals `2)   # oracle: two distinct rows were given`
   - Expected: stored[0].callee_template_id equals `sha256:aa`
   - Expected: stored[1].callee_template_id equals `sha256:zz`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("project a template and fill it with rows given out of order")
val entry = box_template()
val rows = [need("sha256:zz", ["c3:i64"], 30, "call"), need("sha256:aa", ["c3:i64"], 5, "field")]
val f = filled(entry, rows)
step("read the stored rows back")
val stored = slot_rows(f)
expect(stored.len()).to_equal(2)   # oracle: two distinct rows were given
expect(stored[0].callee_template_id).to_equal("sha256:aa")
expect(stored[1].callee_template_id).to_equal("sha256:zz")
```

</details>

#### leaves the original entry untouched

- produce the slot states of the original entry and of the filled copy
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: slot_is_absent(entry) is true
   - Expected: slot_is_absent(f) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("produce the slot states of the original entry and of the filled copy")
val entry = box_template()
val f = filled(entry, one_need_rows(entry))
expect(slot_is_absent(entry)).to_equal(true)
expect(slot_is_absent(f)).to_equal(false)
```

</details>

#### accepts a fill with no rows and records it as filled

- produce the slot state and row count after a fill with no rows
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: slot_is_absent(f) is false
   - Expected: slot_rows(f).len() equals `0)   # oracle: no rows were given`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("produce the slot state and row count after a fill with no rows")
val f = filled(box_template(), [])
expect(slot_is_absent(f)).to_equal(false)
expect(slot_rows(f).len()).to_equal(0)   # oracle: no rows were given
```

</details>

#### a second fill

#### is refused even when the rows are equal, naming the symbol

- fill once
   - Text capture: after_step
- fill again with the same rows
   - Expected: again.is_err() is true
   - Expected: again.unwrap_err() equals `open needs of " + entry.symbol_id + " are already filled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("fill once")
val entry = box_template()
val f = filled(entry, one_need_rows(entry))
step("fill again with the same rows")
val again = generic_template_fill_open_needs_v1(f, one_need_rows(entry))
expect(again.is_err()).to_equal(true)
expect(again.unwrap_err()).to_equal("open needs of " + entry.symbol_id + " are already filled")
```

</details>

#### is refused after a fill with no rows

- produce the verdict of a fill after a fill with no rows
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_template_fill_open_needs_v1(f, one_need_rows(entry)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("produce the verdict of a fill after a fill with no rows")
val entry = box_template()
val f = filled(entry, [])
expect(generic_template_fill_open_needs_v1(f, one_need_rows(entry)).is_err()).to_equal(true)
```

</details>

#### a malformed row

#### refuses the fill and names the symbol and the reason

- run the refused case: the fill with a row naming no callee
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: r.is_err() is true
   - Expected: r.unwrap_err() equals `open needs of " + entry.symbol_id + ": need names no callee template`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("run the refused case: the fill with a row naming no callee")
val entry = box_template()
val r = generic_template_fill_open_needs_v1(entry, [need("", ["c3:i64"], 1, "call")])
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("open needs of " + entry.symbol_id + ": need names no callee template")
```

</details>

#### Editing a body so that it needs one more instance

#### changes the decoded open needs of the template

- fill the same projected template with one need, then with two
   - Exec capture: after_step
- encode both as v3 sections and decode them
   - Expected: wire_after != wire_before is true
   - Expected: rows_before.len() equals `1)   # oracle: one need was filled`
   - Expected: rows_after.len() equals `2)   # oracle: one more need was filled`
   - Expected: rows_after[1].callee_template_id equals `sha256:map`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GENERIC-F1B-002
step("fill the same projected template with one need, then with two")
val entry = box_template()
val before = filled(entry, one_need_rows(entry))
val after = filled(entry, two_need_rows(entry))
step("encode both as v3 sections and decode them")
val wire_before = wire_of([before])
val wire_after = wire_of([after])
val rows_before = slot_rows(generic_template_section_decode_v3(wire_before).unwrap().entries[0])
val rows_after = slot_rows(generic_template_section_decode_v3(wire_after).unwrap().entries[0])
expect(wire_after != wire_before).to_equal(true)
expect(rows_before.len()).to_equal(1)   # oracle: one need was filled
expect(rows_after.len()).to_equal(2)   # oracle: one more need was filled
expect(rows_after[1].callee_template_id).to_equal("sha256:map")
```

</details>

#### changes the key of every instance of that template and of no other template

- build two instances of Box and one instance of an unrelated template
   - Text capture: after_step
- seal and decode a section before the edit and one after it
- compare their keys
   - Expected: instance_key(box, "c3:i64", new_rows) != instance_key(box, "c3:i64", old_rows) is true
   - Expected: instance_key(box, "c4:text", new_rows) != instance_key(box, "c4:text", old_rows) is true
   - Expected: other_old.symbol_id equals `other.symbol_id`
   - Expected: instance_key(other_new, "c3:i64", slot_rows(other_new)) equals `instance_key(other_old, "c3:i64", slot_rows(other_old))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build two instances of Box and one instance of an unrelated template")
val box = box_template()
val other = template("Pair", "T", "T")
val other_rows = [need("sha256:lst", [binder_key(other)], 3, "call")]
val old_rows = one_need_rows(box)
val new_rows = two_need_rows(box)
step("seal and decode a section before the edit and one after it")
val section_old = generic_template_section_decode_v3(wire_of([filled(box, old_rows), filled(other, other_rows)])).unwrap()
val section_new = generic_template_section_decode_v3(wire_of([filled(box, new_rows), filled(other, other_rows)])).unwrap()
step("compare their keys")
expect(instance_key(box, "c3:i64", new_rows) != instance_key(box, "c3:i64", old_rows)).to_equal(true)
expect(instance_key(box, "c4:text", new_rows) != instance_key(box, "c4:text", old_rows)).to_equal(true)
val other_old = section_old.entries[1]
val other_new = section_new.entries[1]
expect(other_old.symbol_id).to_equal(other.symbol_id)
expect(instance_key(other_new, "c3:i64", slot_rows(other_new))).to_equal(instance_key(other_old, "c3:i64", slot_rows(other_old)))
```

</details>

#### keeps the instances of one template apart

- produce the instance keys of Box for two argument types
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: instance_key(box, "c3:i64", rows) != instance_key(box, "c4:text", rows) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("produce the instance keys of Box for two argument types")
val box = box_template()
val rows = one_need_rows(box)
expect(instance_key(box, "c3:i64", rows) != instance_key(box, "c4:text", rows)).to_equal(true)
```

</details>

#### keeps the key of a template when only a call moves

- produce the instance keys of Box with the call at two offsets and with another cause
   - Expected: instance_key(box, "c3:i64", moved) equals `instance_key(box, "c3:i64", here)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("produce the instance keys of Box with the call at two offsets and with another cause")
val box = box_template()
val here = [need("sha256:lst", [binder_key(box)], 10, "field")]
val moved = [need("sha256:lst", [binder_key(box)], 900, "call")]
expect(instance_key(box, "c3:i64", moved)).to_equal(instance_key(box, "c3:i64", here))
```

</details>

#### Renaming a binder

#### changes neither the slot bytes, the identity digest nor the instance keys

- project the same declaration with binder T and with binder U
   - Exec capture: after_step
- build each entry's rows from its own binder id
- compare slot wires, identity digests and instance keys
   - Expected: generic_open_needs_slot_encode_v1(filled_u.open_needs).unwrap() equals `generic_open_needs_slot_encode_v1(filled_t.open_needs).unwrap()`
   - Expected: generic_open_needs_identity_digest_v1(rows_u) equals `generic_open_needs_identity_digest_v1(rows_t)`
   - Expected: instance_key(filled_u, "c3:i64", rows_u) equals `instance_key(filled_t, "c3:i64", rows_t)`
   - Expected: instance_key(filled_u, "c4:text", rows_u) equals `instance_key(filled_t, "c4:text", rows_t)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GENERIC-F1B-003
step("project the same declaration with binder T and with binder U")
val with_t = template("Box", "T", "T")
val with_u = template("Box", "U", "U")
step("build each entry's rows from its own binder id")
val rows_t = two_need_rows(with_t)
val rows_u = two_need_rows(with_u)
val filled_t = filled(with_t, rows_t)
val filled_u = filled(with_u, rows_u)
step("compare slot wires, identity digests and instance keys")
expect(generic_open_needs_slot_encode_v1(filled_u.open_needs).unwrap()).to_equal(generic_open_needs_slot_encode_v1(filled_t.open_needs).unwrap())
expect(generic_open_needs_identity_digest_v1(rows_u)).to_equal(generic_open_needs_identity_digest_v1(rows_t))
expect(instance_key(filled_u, "c3:i64", rows_u)).to_equal(instance_key(filled_t, "c3:i64", rows_t))
expect(instance_key(filled_u, "c4:text", rows_u)).to_equal(instance_key(filled_t, "c4:text", rows_t))
```

</details>

#### keeps the slot frame of the v3 section identical (only the displayed binder name differs in the template table)

- produce the slot frame and the template-table frame of the sections for binders T and U
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: slot_u equals `slot_t`
   - Expected: sealed_values(wire_of([with_u]))[1] != sealed_values(wire_of([with_t]))[1] is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("produce the slot frame and the template-table frame of the sections for binders T and U")
val with_t = filled(template("Box", "T", "T"), two_need_rows(template("Box", "T", "T")))
val with_u = filled(template("Box", "U", "U"), two_need_rows(template("Box", "U", "U")))
val slot_t = sealed_values(wire_of([with_t]))[2]
val slot_u = sealed_values(wire_of([with_u]))[2]
expect(slot_u).to_equal(slot_t)
expect(sealed_values(wire_of([with_u]))[1] != sealed_values(wire_of([with_t]))[1]).to_equal(true)
```

</details>

#### Open needs outside every template identity

#### leaves the template id and all three facet fingerprints alone whatever the slot holds

- take the same template with an absent, a filled-empty and a filled slot
   - Exec capture: after_step
- compare ids and facets
   - Expected: generic_template_id_v2(empty) equals `id`
   - Expected: generic_template_id_v2(full) equals `id`
   - Expected: facets.signature_fingerprint equals `base.signature_fingerprint`
   - Expected: facets.bound_fingerprint equals `base.bound_fingerprint`
   - Expected: facets.body_fingerprint equals `base.body_fingerprint`
   - Expected: facets.template_id equals `base.template_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GENERIC-F1B-004
step("take the same template with an absent, a filled-empty and a filled slot")
val absent = box_template()
val empty = filled(absent, [])
val full = filled(absent, two_need_rows(absent))
step("compare ids and facets")
val id = generic_template_id_v2(absent)
expect(generic_template_id_v2(empty)).to_equal(id)
expect(generic_template_id_v2(full)).to_equal(id)
val base = generic_template_facets_v2(absent).unwrap()
for other in [empty, full]:
    val facets = generic_template_facets_v2(other).unwrap()
    expect(facets.signature_fingerprint).to_equal(base.signature_fingerprint)
    expect(facets.bound_fingerprint).to_equal(base.bound_fingerprint)
    expect(facets.body_fingerprint).to_equal(base.body_fingerprint)
    expect(facets.template_id).to_equal(base.template_id)
```

</details>

#### leaves the section digest of the carried v2 table alone

- produce the digest of the carried v2 table with the slot absent and filled
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: section_of([full]).digest equals `section_of([absent]).digest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("produce the digest of the carried v2 table with the slot absent and filled")
val absent = box_template()
val full = filled(absent, two_need_rows(absent))
expect(section_of([full]).digest).to_equal(section_of([absent]).digest)
```

</details>

#### Readers of the wrong schema miss

#### a v2 reader given v3 bytes

#### misses on the v2 magic check

- produce the ok flag and error text of the v2 decoder on a v3 wire
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: r.ok is false
   - Expected: r.error equals `v2 magic required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("produce the ok flag and error text of the v2 decoder on a v3 wire")
# @req REQ-GENERIC-F1B-005
val entry = box_template()
val wire = wire_of([filled(entry, one_need_rows(entry))])
val r = generic_template_section_decode_v2(wire)
expect(r.ok).to_equal(false)
expect(r.error).to_equal("v2 magic required")
```

</details>

#### a v3 reader given older bytes

#### refuses a v2 section

- run the refused case: the v3 decoder on a v2 wire
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: v3_refusal(v2) equals `v3 magic required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("run the refused case: the v3 decoder on a v2 wire")
val entry = box_template()
val v2 = generic_template_section_encode_v2(section_of([entry])).unwrap()
expect(v3_refusal(v2)).to_equal("v3 magic required")
```

</details>

#### refuses a v1 section

- run the refused case: the v3 decoder on a v1 wire
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: v3_refusal(v1) equals `v3 magic required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("run the refused case: the v3 decoder on a v1 wire")
val v1_entry = project_generic_template_v1(decl("Box", "T", "T")).unwrap()
val v1 = generic_template_section_encode_v1(build_generic_template_section_v1([v1_entry]))
expect(v3_refusal(v1)).to_equal("v3 magic required")
```

</details>

#### Round trip of a v3 section

#### re-encodes byte for byte what it decoded, with a non-ASCII symbol name

- fill a template named 箱 and seal it
   - Exec capture: after_step
- decode, then encode again
   - Expected: generic_template_section_encode_v3(back).unwrap() equals `wire`
   - Expected: back.entries[0].symbol_id equals `entry.symbol_id`
   - Expected: slot_rows(back.entries[0]).len() equals `2)   # oracle: two needs were filled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GENERIC-F1B-006
step("fill a template named 箱 and seal it")
val entry = template("箱", "T", "T")
val wire = wire_of([filled(entry, two_need_rows(entry))])
step("decode, then encode again")
val back = generic_template_section_decode_v3(wire).unwrap()
expect(generic_template_section_encode_v3(back).unwrap()).to_equal(wire)
expect(back.entries[0].symbol_id).to_equal(entry.symbol_id)
expect(slot_rows(back.entries[0]).len()).to_equal(2)   # oracle: two needs were filled
```

</details>

#### keeps an absent slot and a filled-empty slot apart on the wire and after decoding

- seal one section of two templates, one never filled and one filled with no rows
   - Exec capture: after_step
- decode and look at each slot
   - Expected: back.entries.len() equals `2)   # oracle: two templates were sealed`
   - Expected: slot_is_absent(back.entries[0]) is true
   - Expected: slot_is_absent(back.entries[1]) is false
   - Expected: slot_rows(back.entries[1]).len() equals `0)   # oracle: filled with no rows`
   - Expected: generic_template_section_encode_v3(back).unwrap() equals `wire`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("seal one section of two templates, one never filled and one filled with no rows")
val never = template("Aaa", "T", "T")
val none = filled(template("Bbb", "T", "T"), [])
val wire = wire_of([never, none])
step("decode and look at each slot")
val back = generic_template_section_decode_v3(wire).unwrap()
expect(back.entries.len()).to_equal(2)   # oracle: two templates were sealed
expect(slot_is_absent(back.entries[0])).to_equal(true)
expect(slot_is_absent(back.entries[1])).to_equal(false)
expect(slot_rows(back.entries[1]).len()).to_equal(0)   # oracle: filled with no rows
expect(generic_template_section_encode_v3(back).unwrap()).to_equal(wire)
```

</details>

#### carries the template table digest through unchanged

- produce the table digest before and after the round trip
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: back.digest equals `section.digest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("produce the table digest before and after the round trip")
val entry = box_template()
val section = section_of([filled(entry, one_need_rows(entry))])
val back = generic_template_section_decode_v3(generic_template_section_encode_v3(section).unwrap()).unwrap()
expect(back.digest).to_equal(section.digest)
```

</details>

#### Encoding refusals

#### refuses a section whose v2 table has a wrong seal

- run the refused case: encoding a section whose table digest is wrong
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: r.is_err() is true
   - Expected: r.unwrap_err() equals `invalid v2 section seal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("run the refused case: encoding a section whose table digest is wrong")
val entry = box_template()
val section = section_of([entry])
val bad = GenericTemplateSectionV1(entries: section.entries, digest: "bad seal")
val r = generic_template_section_encode_v3(bad)
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("invalid v2 section seal")
```

</details>

#### refuses an entry whose slot holds a malformed row and names the symbol

- put an unchecked filled slot with an empty callee into an entry
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: r.is_err() is true
   - Expected: r.unwrap_err() equals `open needs of " + entry.symbol_id + ": need names no callee template`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("put an unchecked filled slot with an empty callee into an entry")
val entry = box_template()
var broken = entry
broken.open_needs = GenericOpenNeedsSlotV1.Filled(rows: [need("", ["c3:i64"], 1, "call")])
val r = generic_template_section_encode_v3(section_of([broken]))
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("open needs of " + entry.symbol_id + ": need names no callee template")
```

</details>

#### Refusals of the v3 decoder

#### rule: the bytes must be well-framed

#### refuses malformed framing and says so

- decode a wire whose first frame header has no colon
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: v3_refusal("5") equals `malformed v3 frame: frame header has no ':'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @manual: folded
step("decode a wire whose first frame header has no colon")
expect(v3_refusal("5")).to_equal("malformed v3 frame: frame header has no ':'")
```

</details>

#### rule: a seal, a magic and an inner table must be present

#### refuses fewer than three frames

- run the refused case: the v3 decoder on a two-frame wire
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: v3_refusal(generic_need_frames_v1(["a", "b"])) equals `v3 magic required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("run the refused case: the v3 decoder on a two-frame wire")
expect(v3_refusal(generic_need_frames_v1(["a", "b"]))).to_equal("v3 magic required")
```

</details>

#### refuses a wrong magic even when the seal is right

- run the refused case: the v3 decoder on a wrongly named magic under a valid seal
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: v3_refusal(wire) equals `v3 magic required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("run the refused case: the v3 decoder on a wrongly named magic under a valid seal")
val wire = reseal(["generic-template-section/v9", "inner"])
expect(v3_refusal(wire)).to_equal("v3 magic required")
```

</details>

#### rule: the seal must match every frame after it

#### refuses a wire whose seal was altered

- take a valid wire and replace its seal by another digest
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: v3_refusal(tampered) equals `v3 section seal mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("take a valid wire and replace its seal by another digest")
val entry = box_template()
val values = sealed_values(wire_of([filled(entry, one_need_rows(entry))]))
val tampered = generic_need_frames_v1([sha256_text("not the body")]) + generic_need_frames_v1(values)
expect(v3_refusal(tampered)).to_equal("v3 section seal mismatch")
```

</details>

#### refuses a wire whose body changed after sealing

- flip one needs-table byte of a valid wire without re-sealing
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: tampered != wire is true
   - Expected: v3_refusal(tampered) equals `v3 section seal mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("flip one needs-table byte of a valid wire without re-sealing")
val entry = box_template()
val wire = wire_of([filled(entry, one_need_rows(entry))])
val tampered = wire.replace("sha256:lst", "sha256:lsX")
expect(tampered != wire).to_equal(true)
expect(v3_refusal(tampered)).to_equal("v3 section seal mismatch")
```

</details>

#### rule: the carried v2 table must itself be valid

#### refuses a corrupt inner table behind a correct seal

- run the refused case: the v3 decoder on a garbage inner table
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: verdict equals `v3 template table: invalid v2 UTF8 frame`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("run the refused case: the v3 decoder on a garbage inner table")
val wire = reseal([GENERIC_TEMPLATE_SECTION_MAGIC_V3, "garbage"])
val verdict = v3_refusal(wire)
expect(verdict).to_equal("v3 template table: invalid v2 UTF8 frame")
```

</details>

#### rule: there is exactly one slot per template

#### refuses a wire with a missing slot

- run the refused case: the v3 decoder on a wire with no slot for its entry
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: v3_refusal(wire) equals `v3 needs table does not match the template table`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("run the refused case: the v3 decoder on a wire with no slot for its entry")
val entry = box_template()
val values = sealed_values(wire_of([filled(entry, one_need_rows(entry))]))
val wire = reseal([values[0], values[1]])
expect(v3_refusal(wire)).to_equal("v3 needs table does not match the template table")
```

</details>

#### refuses a wire with one slot too many

- run the refused case: the v3 decoder on a wire with two slots for one entry
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: v3_refusal(wire) equals `v3 needs table does not match the template table`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("run the refused case: the v3 decoder on a wire with two slots for one entry")
val entry = box_template()
val values = sealed_values(wire_of([filled(entry, one_need_rows(entry))]))
val wire = reseal([values[0], values[1], values[2], values[2]])
expect(v3_refusal(wire)).to_equal("v3 needs table does not match the template table")
```

</details>

#### rule: every slot must decode

#### refuses a corrupt slot and names the symbol

- replace the slot of a valid wire by an unknown state and re-seal
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: v3_refusal(wire) equals `open needs of " + entry.symbol_id + ": unknown open-needs state 'later'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("replace the slot of a valid wire by an unknown state and re-seal")
val entry = box_template()
val values = sealed_values(wire_of([filled(entry, one_need_rows(entry))]))
val wire = reseal([values[0], values[1], generic_need_frames_v1(["later"])])
expect(v3_refusal(wire)).to_equal("open needs of " + entry.symbol_id + ": unknown open-needs state 'later'")
```

</details>

#### refuses a slot that is valid but not in canonical form

- write two rows in reverse order into the slot and re-seal
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: v3_refusal(wire) equals `open needs of " + entry.symbol_id + ": open-needs slot is not in canonical form`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("write two rows in reverse order into the slot and re-seal")
val entry = box_template()
val values = sealed_values(wire_of([entry]))
val z = generic_need_frames_v1(["z", "1", "2", "call", generic_need_frames_v1(["k"])])
val a = generic_need_frames_v1(["a", "1", "2", "call", generic_need_frames_v1(["k"])])
val wire = reseal([values[0], values[1], generic_need_frames_v1(["filled", z, a])])
expect(v3_refusal(wire)).to_equal("open needs of " + entry.symbol_id + ": open-needs slot is not in canonical form")
```

</details>

#### a valid wire

#### is accepted

- produce the verdict of the v3 decoder on an untampered wire
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: v3_refusal(wire_of([filled(entry, one_need_rows(entry))])) equals `ACCEPTED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("produce the verdict of the v3 decoder on an untampered wire")
val entry = box_template()
expect(v3_refusal(wire_of([filled(entry, one_need_rows(entry))]))).to_equal("ACCEPTED")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/language/type_system/no_any_inference_plan.md (rows S3-F0..F10, row S3-F1)`
- **Design:** `doc/05_design/compiler/cache/generic_instance_tldr_trace.md (sections 3, 4, 5, 9, 14)`
- **Research:** `doc/01_research/compiler/compile_speed/mono_instance_census_2026-10-19.md (instance census this stage serves)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-GENERIC-F1B-001`
- `REQ-GENERIC-F1B-002`
- `REQ-GENERIC-F1B-003`
- `REQ-GENERIC-F1B-004`
- `REQ-GENERIC-F1B-005`
- `REQ-GENERIC-F1B-006`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1f35907ffc0bca2fe94e9b503008da9a20a760df905e7fb26e5334c0bf56520a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1f35907ffc0bca2fe94e9b503008da9a20a760df905e7fb26e5334c0bf56520a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1f35907ffc0bca2fe94e9b503008da9a20a760df905e7fb26e5334c0bf56520a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **98/100**; effective score: **98/100**; blockers: **0**.

SSpec documentization score: 98/100
source: 01_unit/compiler/cache/generic_template_section_v3_spec.spl
mirror: doc/06_spec/01_unit/compiler/cache/generic_template_section_v3_spec.md (current)
findings: 1 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=80
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/cache/generic_template_section_v3_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
