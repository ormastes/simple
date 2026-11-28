# Generic template section v3 (`generic_template_section_v3`)

> Purpose: pin the behaviour of the section schema that carries each generic

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

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

- project the declaration Box<T> and read its slot
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: slot_is_absent(box_template()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("project the declaration Box<T> and read its slot")
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

- fill a copy of the Box template and read both slots
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: slot_is_absent(entry) is true
   - Expected: slot_is_absent(f) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("fill a copy of the Box template and read both slots")
val entry = box_template()
val f = filled(entry, one_need_rows(entry))
expect(slot_is_absent(entry)).to_equal(true)
expect(slot_is_absent(f)).to_equal(false)
```

</details>

#### accepts a fill with no rows and records it as filled

- fill the Box template with an empty row list
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: slot_is_absent(f) is false
   - Expected: slot_rows(f).len() equals `0)   # oracle: no rows were given`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("fill the Box template with an empty row list")
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

- fill the Box template twice, first with no rows, then with one row
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: generic_template_fill_open_needs_v1(f, one_need_rows(entry)).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("fill the Box template twice, first with no rows, then with one row")
val entry = box_template()
val f = filled(entry, [])
expect(generic_template_fill_open_needs_v1(f, one_need_rows(entry)).is_err()).to_equal(true)
```

</details>

#### a malformed row

#### refuses the fill and names the symbol and the reason

- fill the Box template with a row whose callee is empty
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: r.is_err() is true
   - Expected: r.unwrap_err() equals `open needs of " + entry.symbol_id + ": need names no callee template`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("fill the Box template with a row whose callee is empty")
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
val rows_before = slot_rows(generic_template_section_decode_v3(wire_before).unwrap().section.entries[0])
val rows_after = slot_rows(generic_template_section_decode_v3(wire_after).unwrap().section.entries[0])
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
val other_old = section_old.section.entries[1]
val other_new = section_new.section.entries[1]
expect(other_old.symbol_id).to_equal(other.symbol_id)
expect(instance_key(other_new, "c3:i64", slot_rows(other_new))).to_equal(instance_key(other_old, "c3:i64", slot_rows(other_old)))
```

</details>

#### keeps the instances of one template apart

- build the instance keys of Box for i64 and for text
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: instance_key(box, "c3:i64", rows) != instance_key(box, "c4:text", rows) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build the instance keys of Box for i64 and for text")
val box = box_template()
val rows = one_need_rows(box)
expect(instance_key(box, "c3:i64", rows) != instance_key(box, "c4:text", rows)).to_equal(true)
```

</details>

#### keeps the key of a template when only a call moves

- build the instance keys of Box with the call at offset 10 and at 900
   - Expected: instance_key(box, "c3:i64", moved) equals `instance_key(box, "c3:i64", here)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build the instance keys of Box with the call at offset 10 and at 900")
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

- seal Box<T> and Box<U> with their own binder keys and compare the frames
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: slot_u equals `slot_t`
   - Expected: sealed_values(wire_of([with_u]))[1] != sealed_values(wire_of([with_t]))[1] is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("seal Box<T> and Box<U> with their own binder keys and compare the frames")
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

- build the table digest with the slot absent and with two needs
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: section_of([full]).digest equals `section_of([absent]).digest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build the table digest with the slot absent and with two needs")
val absent = box_template()
val full = filled(absent, two_need_rows(absent))
expect(section_of([full]).digest).to_equal(section_of([absent]).digest)
```

</details>

#### Readers of the wrong schema miss

#### a v2 reader given v3 bytes

#### misses on the v2 magic check

- decode a v3 wire with the v2 decoder
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: r.ok is false
   - Expected: r.error equals `v2 magic required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode a v3 wire with the v2 decoder")
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

- decode a v2 wire with the v3 decoder
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: v3_refusal(v2) equals `v3 magic required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode a v2 wire with the v3 decoder")
val entry = box_template()
val v2 = generic_template_section_encode_v2(section_of([entry])).unwrap()
expect(v3_refusal(v2)).to_equal("v3 magic required")
```

</details>

#### refuses a v1 section

- decode a v1 wire with the v3 decoder
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: v3_refusal(v1) equals `v3 magic required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode a v1 wire with the v3 decoder")
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
   - Expected: generic_template_section_encode_v3(back.section).unwrap() equals `wire`
   - Expected: back.section.entries[0].symbol_id equals `entry.symbol_id`
   - Expected: slot_rows(back.section.entries[0]).len() equals `2)   # oracle: two needs were filled`


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
expect(generic_template_section_encode_v3(back.section).unwrap()).to_equal(wire)
expect(back.section.entries[0].symbol_id).to_equal(entry.symbol_id)
expect(slot_rows(back.section.entries[0]).len()).to_equal(2)   # oracle: two needs were filled
```

</details>

#### keeps an absent slot and a filled-empty slot apart on the wire and after decoding

- seal one section of two templates, one never filled and one filled with no rows
   - Exec capture: after_step
- decode and look at each slot
   - Expected: back.section.entries.len() equals `2)   # oracle: two templates were sealed`
   - Expected: slot_is_absent(back.section.entries[0]) is true
   - Expected: slot_is_absent(back.section.entries[1]) is false
   - Expected: slot_rows(back.section.entries[1]).len() equals `0)   # oracle: filled with no rows`
   - Expected: generic_template_section_encode_v3(back.section).unwrap() equals `wire`


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
expect(back.section.entries.len()).to_equal(2)   # oracle: two templates were sealed
expect(slot_is_absent(back.section.entries[0])).to_equal(true)
expect(slot_is_absent(back.section.entries[1])).to_equal(false)
expect(slot_rows(back.section.entries[1]).len()).to_equal(0)   # oracle: filled with no rows
expect(generic_template_section_encode_v3(back.section).unwrap()).to_equal(wire)
```

</details>

#### carries the template table digest through unchanged

- encode and decode a one-need section and compare the table digests
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: back.section.digest equals `section.digest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("encode and decode a one-need section and compare the table digests")
val entry = box_template()
val section = section_of([filled(entry, one_need_rows(entry))])
val back = generic_template_section_decode_v3(generic_template_section_encode_v3(section).unwrap()).unwrap()
expect(back.section.digest).to_equal(section.digest)
```

</details>

#### Encoding refusals

#### refuses a section whose v2 table has a wrong seal

- encode a section whose digest is the text bad seal
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: r.is_err() is true
   - Expected: r.unwrap_err() equals `invalid v2 section seal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("encode a section whose digest is the text bad seal")
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

- decode the two frames a and b
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: v3_refusal(generic_need_frames_v1(["a", "b"])) equals `v3 magic required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode the two frames a and b")
expect(v3_refusal(generic_need_frames_v1(["a", "b"]))).to_equal("v3 magic required")
```

</details>

#### refuses a wrong magic even when the seal is right

- decode a correctly sealed wire naming magic v9
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: v3_refusal(wire) equals `v3 magic required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode a correctly sealed wire naming magic v9")
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

- decode a correctly sealed wire whose inner table is the text garbage
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: verdict equals `v3 template table: invalid v2 UTF8 frame`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode a correctly sealed wire whose inner table is the text garbage")
val wire = reseal([GENERIC_TEMPLATE_SECTION_MAGIC_V3, "garbage"])
val verdict = v3_refusal(wire)
expect(verdict).to_equal("v3 template table: invalid v2 UTF8 frame")
```

</details>

#### rule: there is exactly one slot per template

#### refuses a wire with a missing slot

- decode a re-sealed wire with the slot frame removed
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: v3_refusal(wire) equals `v3 needs table does not match the template table`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode a re-sealed wire with the slot frame removed")
val entry = box_template()
val values = sealed_values(wire_of([filled(entry, one_need_rows(entry))]))
val wire = reseal([values[0], values[1]])
expect(v3_refusal(wire)).to_equal("v3 needs table does not match the template table")
```

</details>

#### refuses a wire with one slot too many

- decode a re-sealed wire with the slot frame doubled
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: v3_refusal(wire) equals `v3 needs table does not match the template table`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode a re-sealed wire with the slot frame doubled")
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

- decode an untampered one-need wire
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: v3_refusal(wire_of([filled(entry, one_need_rows(entry))])) equals `ACCEPTED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode an untampered one-need wire")
val entry = box_template()
expect(v3_refusal(wire_of([filled(entry, one_need_rows(entry))]))).to_equal("ACCEPTED")
```

</details>

#### Byte bound of a v3 section

#### refuses input one byte over the bound before reading any frame

- build a filler of bound + 1 bytes by repeated doubling and decode it
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: over.byte_len() equals `V3_BOUND_BYTES + 1`
   - Expected: v3_refusal(over) equals `v3 byte bound exceeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build a filler of bound + 1 bytes by repeated doubling and decode it")
val over = filler_of(V3_BOUND_BYTES + 1)
expect(over.byte_len()).to_equal(V3_BOUND_BYTES + 1)
expect(v3_refusal(over)).to_equal("v3 byte bound exceeded")
```

</details>

#### lets input of exactly the bound through to framing, which refuses it as garbage

- decode a filler of exactly bound bytes
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: exact.byte_len() equals `V3_BOUND_BYTES`
   - Expected: v3_refusal(exact) equals `malformed v3 frame: frame header has no ':'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode a filler of exactly bound bytes")
val exact = filler_of(V3_BOUND_BYTES)
expect(exact.byte_len()).to_equal(V3_BOUND_BYTES)
expect(v3_refusal(exact)).to_equal("malformed v3 frame: frame header has no ':'")
```

</details>

#### refuses to encode a section whose sealed frames exceed the bound

- fill one entry with a need whose argument key is bound + 1 bytes long
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: r.is_err() is true
   - Expected: r.unwrap_err() equals `v3 byte bound exceeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("fill one entry with a need whose argument key is bound + 1 bytes long")
val entry = box_template()
var big = entry
big.open_needs = GenericOpenNeedsSlotV1.Filled(rows: [need("sha256:lst", [filler_of(V3_BOUND_BYTES + 1)], 1, "call")])
val r = generic_template_section_encode_v3(section_of([big]))
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("v3 byte bound exceeded")
```

</details>

#### Readers of older schemas given v3 bytes

#### makes the v1 reader fail closed on a v3 wire

- decode a v3 wire with the v1 decoder
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: r.ok is false
   - Expected: r.error equals `V1_REFUSAL_OF_V3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("decode a v3 wire with the v1 decoder")
val entry = box_template()
val r = generic_template_section_decode_v1(wire_of([filled(entry, one_need_rows(entry))]))
expect(r.ok).to_equal(false)
expect(r.error).to_equal(V1_REFUSAL_OF_V3)
```

</details>

#### Seal of a v3 section

#### equals the seal of the decoded wire and the first frame of the wire

- seal a filled section, encode it, decode it
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: decoded.seal equals `computed`
   - Expected: generic_need_frames_read_v1(wire).unwrap()[0] equals `computed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("seal a filled section, encode it, decode it")
val entry = box_template()
val section = section_of([filled(entry, one_need_rows(entry))])
val wire = generic_template_section_encode_v3(section).unwrap()
val decoded = generic_template_section_decode_v3(wire).unwrap()
val computed = generic_template_section_seal_v3(section).unwrap()
expect(decoded.seal).to_equal(computed)
expect(generic_need_frames_read_v1(wire).unwrap()[0]).to_equal(computed)
```

</details>

#### moves with the open needs while the table digest and the template id stay

- seal the same template with an absent slot, a filled-empty slot and a one-row slot
   - Exec capture: after_step
   - Evidence: execution result verified by 6 expected checks
   - Expected: seal_empty != seal_absent is true
   - Expected: seal_one != seal_empty is true
   - Expected: seal_one != seal_absent is true
   - Expected: section_of([one]).digest equals `section_of([absent]).digest`
   - Expected: section_of([empty]).digest equals `section_of([absent]).digest`
   - Expected: generic_template_id_v2(one) equals `generic_template_id_v2(absent)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("seal the same template with an absent slot, a filled-empty slot and a one-row slot")
val absent = box_template()
val empty = filled(absent, [])
val one = filled(absent, one_need_rows(absent))
val seal_absent = generic_template_section_seal_v3(section_of([absent])).unwrap()
val seal_empty = generic_template_section_seal_v3(section_of([empty])).unwrap()
val seal_one = generic_template_section_seal_v3(section_of([one])).unwrap()
expect(seal_empty != seal_absent).to_equal(true)
expect(seal_one != seal_empty).to_equal(true)
expect(seal_one != seal_absent).to_equal(true)
expect(section_of([one]).digest).to_equal(section_of([absent]).digest)
expect(section_of([empty]).digest).to_equal(section_of([absent]).digest)
expect(generic_template_id_v2(one)).to_equal(generic_template_id_v2(absent))
```

</details>

#### is refused for an invalid section

- seal a section whose table digest is wrong
   - Text capture: after_step
   - Evidence: text output verified by 2 expected checks
   - Expected: r.is_err() is true
   - Expected: r.unwrap_err() equals `invalid v2 section seal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("seal a section whose table digest is wrong")
val section = section_of([box_template()])
val bad = GenericTemplateSectionV1(entries: section.entries, digest: "bad seal")
val r = generic_template_section_seal_v3(bad)
expect(r.is_err()).to_equal(true)
expect(r.unwrap_err()).to_equal("invalid v2 section seal")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
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

- Canonical SPipe generation for source `1220bc2c13459351c1bddd71c36c76358a41a44bf21a076f78734537665e7a63`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1220bc2c13459351c1bddd71c36c76358a41a44bf21a076f78734537665e7a63`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1220bc2c13459351c1bddd71c36c76358a41a44bf21a076f78734537665e7a63`  
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
