# `aspect-decl|`: the advice declarations a module publishes in its TLDR

> Purpose: document and pin

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `aspect-decl|`: the advice declarations a module publishes in its TLDR

Purpose: document and pin

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/aop/aspect_decl_section_v1_spec.spl` |
| Updated | 2026-11-28 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: document and pin
`src/compiler/00.common/cache_contract/aspect_decl_section_v1.spl`, the codec
of the `aspect-decl|` module TLDR section (aspect plan stage AW-1). A module
that declares advice writes one row per declaration into its own TLDR. A file
that may be advised later reads those rows instead of another file's HIR or a
process-global registry, so the cache can tell which files an advice edit
touches without compiling anything.

Audience: compiler engineers who produce or consume the section (the TLDR
writer, the later `advice_index` and weave-plan stages) and reviewers checking
that a damaged or foreign section can never be read as "this module declares
no advice".

## What a section holds

| Part | Meaning |
|------|---------|
| seal | sha256 over every byte after it; integrity only |
| leaf digest | the module's aspect interface digest (rows, handler signature, effects; no body); the input of the directory `aspect_root_digest` |
| row | family (`logical` or `mir`), `AdviceId`, handler, form, mode, activation, selector text and selector id, scope id, order, the three contract flags, signature digest, effects digest |
| `advice.body` facet | the handler body digest; excluded from the row digest and from the leaf |

`form` is the declaration as written: the advice form of a mir row (`before`,
`after`, `around`) or the join-point kind of a logical row (`forward`). `mode`
is where the advice runs: the form of a mir row, and `before` for a logical
row, which is always woven as a call at the start of the forwarder.
`activation` is the declared weave mode (`static` unless a registry mode is
named).

`AdviceId` names a declaration by module, family, handler and the 0-based
occurrence of that handler in that family. It is not the position of the
declaration in the module, so adding or removing another advice leaves it
unchanged; `family_inventory_index` is that position and does shift.

A row digest (`aspect_decl_row_digest_v1`) is the identity of a declaration.
Editing an advice body changes only the facet. Editing a selector changes the
row digest. Both rules are proved here on hand-built rows and again on real
lowered modules in `aspect_decl_section_writer_v1_spec.spl`.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/aop/aspect_decl_section_v1_spec.spl`
   from the repository root. No fixture file and no host fact is read.
2. Measure coverage with
   `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<f> <seed> run <this spec>`
   (doc/07_guide/infra/testing/coverage.md).

## Reading a decode result

| status | When | What the reader does |
|--------|------|----------------------|
| `ok` | size, framing, magic, seal, counts and every row verified | uses the section |
| `miss` | no section, or a seal whose algorithm this reader cannot verify | recomputes; nothing is wrong |
| `reject` | malformed, truncated, over a limit, tampered, unknown non-optional field | recomputes and may report the reason |

A result that is not `ok` always carries an empty section.

## Lifecycle

Research: doc/01_research/local/dir_tldr_aspect.md
Plan: doc/03_plan/compiler/aspect_cache/aspect_tldr_async_trace_plan.md (AW-1)
Architecture: doc/04_architecture/compiler/aspect_dynload/typed_facet_pipeline_2026-08-22.md
Design: doc/05_design/compiler/cache/aspect_tldr_async_trace.md (section 3)

## Decision inventory (MC/DC)

Function names refer to `aspect_decl_section_v1.spl`.

| Function | Decision | Covering scenario |
|----------|----------|-------------------|
| `aspect_section_count_v1` | empty or longer than 12 digits; byte below `0` or above `9` | "a count is 1 to 12 decimal digits" |
| `aspect_section_frames_read_v1` | width scan stops at end of data, at 12 digits, at `:`; bad width, missing `:`, 13th digit, value overruns | "a frame list is read back value for value", "bytes outside a frame invalidate the whole list" |
| `aspect_section_seal_status_v1` | unparsable seal; algorithm is not sha256; text differs | "a seal verifies only for its own bytes and its own algorithm" |
| `aspect_body_span_digest_v1` | negative start, empty span, span past the end; name absent | "a body digest covers exactly the function's own span" |
| `aspect_decl_row_digest_v1` | key is `body` | "an advice body edit changes only the body facet" |
| `aspect_decl_row_v1` | family is `mir` | "a resolved handler becomes one row of its family" |
| `aspect_decl_section_of_semantic_v1` | handler has no digest; digest is empty; handler already declared in this family | "a handler without a body digest is an error", "two declarations of one handler get different advice ids" |
| `aspect_decl_section_encode_v1` | row limit; head field limit; row field limit; section limit | "encoding refuses every over-limit section" |
| `_int_v1` | leading `-`; bad magnitude; bad number | "order may be negative", "a row with a bad number or flag is rejected" |
| `_row_decode_v1` | known key; duplicate; optional `?` key; missing key; flag not `1` and not `0`; index or order unreadable; index negative | "an unknown optional field is ignored", "an unknown mandatory field is rejected", "a row with a bad number or flag is rejected" |
| `aspect_decl_section_decode_v1` | size; framing; fewer than six values; magic; seal miss; seal reject; count unreadable; count over limit; rows run out; pair count unreadable or overrunning; row error; trailing values | the `decode` scenarios |
| `aspect_decl_section_of_entries_v1` | entry has the kind prefix; none; more than one | "a module TLDR carries exactly one section" |

Exclusions: none.

## Compatibility and limitations

Text is measured in bytes everywhere in this codec. The surrounding module
TLDR record counts characters, so the TLDR round trip here uses ASCII; the
non-ASCII round trip is proved on the section text itself.
The scope id is the same value in every row: no source syntax declares an
advice scope yet.

## Scenarios

### aspect section framing

#### a frame list is read back value for value

- Frame an empty value, an ASCII value and a non-ASCII value, then read the frames
- The three values come back unchanged; the non-ASCII width is its byte width
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: frames.is_some() is true
   - Expected: frames.unwrap() equals `["", "submit_view", "결제::Zahlung"]`
   - Expected: aspect_section_frame_v1("결제") equals `6:결제`
   - Expected: aspect_section_frames_read_v1("").unwrap() equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-CODEC
step("Frame an empty value, an ASCII value and a non-ASCII value, then read the frames")
val wire = aspect_section_frame_v1("") + aspect_section_frame_v1("submit_view") +
    aspect_section_frame_v1("결제::Zahlung")
val frames = aspect_section_frames_read_v1(wire)
step("The three values come back unchanged; the non-ASCII width is its byte width")
expect(frames.is_some()).to_equal(true)
expect(frames.unwrap()).to_equal(["", "submit_view", "결제::Zahlung"])
expect(aspect_section_frame_v1("결제")).to_equal("6:결제")
expect(aspect_section_frames_read_v1("").unwrap()).to_equal([])
```

</details>

#### a count is 1 to 12 decimal digits

- Parse well-formed counts, an empty count, a 13 digit count and non-digit bytes
- Only the first three are counts; everything else is -1
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: parsed equals `[0, 7, 999999999999, -1, -1, -1, -1, -1]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-CODEC
step("Parse well-formed counts, an empty count, a 13 digit count and non-digit bytes")
val parsed = [aspect_section_count_v1("0"), aspect_section_count_v1("007"),
    aspect_section_count_v1("999999999999"), aspect_section_count_v1(""),
    aspect_section_count_v1("1234567890123"), aspect_section_count_v1("1/"),
    aspect_section_count_v1("1:"), aspect_section_count_v1("-1")]
step("Only the first three are counts; everything else is -1")
expect(parsed).to_equal([0, 7, 999999999999, -1, -1, -1, -1, -1])
```

</details>

#### bytes outside a frame invalidate the whole list

- Read a width with no colon, a non-digit width, a 13 digit width and an overrunning value
- Each read fails and returns no value, even though a first frame was well formed
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: result.is_none() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FAILCLOSED
step("Read a width with no colon, a non-digit width, a 13 digit width and an overrunning value")
val results = [aspect_section_frames_read_v1("3:abc12"), aspect_section_frames_read_v1("3:abcxy:"),
    aspect_section_frames_read_v1("1234567890123:"), aspect_section_frames_read_v1("5:ab"),
    aspect_section_frames_read_v1("3:abc:")]
step("Each read fails and returns no value, even though a first frame was well formed")
for result in results:
    expect(result.is_none()).to_equal(true)
```

</details>

#### a seal verifies only for its own bytes and its own algorithm

- Seal a body, then check it against the same body, another body and foreign seals
- Same body is ok, another body is a reject, a known other algorithm and an unknown one are a miss
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: seal equals `"sha256:" + sha256_text("body")`
   - Expected: statuses equals `[ASPECT_SECTION_OK_V1, ASPECT_SECTION_REJECT_V1,`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FAILCLOSED
step("Seal a body, then check it against the same body, another body and foreign seals")
val seal = aspect_section_seal_v1("body")
val statuses = [aspect_section_seal_status_v1(seal, "body"),
    aspect_section_seal_status_v1(seal, "other body"),
    aspect_section_seal_status_v1("blake3:" + sha256_text("body"), "body"),
    aspect_section_seal_status_v1("md5:0123456789abcdef0123456789abcdef", "body"),
    aspect_section_seal_status_v1("not a digest", "body")]
step("Same body is ok, another body is a reject, a known other algorithm and an unknown one are a miss")
expect(seal).to_equal("sha256:" + sha256_text("body"))
expect(statuses).to_equal([ASPECT_SECTION_OK_V1, ASPECT_SECTION_REJECT_V1,
    ASPECT_SECTION_MISS_V1, ASPECT_SECTION_MISS_V1, ASPECT_SECTION_MISS_V1])
```

</details>

### aspect declaration identities

#### a body digest covers exactly the function's own span

- Digest the span of `observe` in a two-function source, then edit each function in turn
- Trailing blank lines and an edit of the other function leave it equal; a body edit changes it
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: base.byte_len() equals `64)  # oracle: sha256 hex width`
   - Expected: padded equals `base`
   - Expected: aspect_body_span_digest_v1(other_edit, start, other_edit.byte_len(), "observe") equals `base`
   - Expected: aspect_body_span_digest_v1(body_edit, start, body_edit.byte_len(), "observe") == base is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FACETS
step("Digest the span of `observe` in a two-function source, then edit each function in turn")
val head = "fn other():\n    1\n\n"
val source = head + "fn observe():\n    return\n"
val start = head.byte_len()
val base = aspect_body_span_digest_v1(source, start, source.byte_len(), "observe")
val padded = aspect_body_span_digest_v1(source + "\n\n", start, source.byte_len() + 2, "observe")
val other_edit = "fn other():\n    2\n\n" + "fn observe():\n    return\n"
val body_edit = head + "fn observe():\n    pass\n"
step("Trailing blank lines and an edit of the other function leave it equal; a body edit changes it")
expect(base.byte_len()).to_equal(64)  # oracle: sha256 hex width
expect(padded).to_equal(base)
expect(aspect_body_span_digest_v1(other_edit, start, other_edit.byte_len(), "observe")).to_equal(base)
expect(aspect_body_span_digest_v1(body_edit, start, body_edit.byte_len(), "observe") == base).to_equal(false)
```

</details>

#### a span that is not this function's declaration has no digest

- Ask for a negative start, an empty span, a span past the end and a span of another function
- Every one is the empty digest, which the section builder refuses
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: digests equals `["", "", "", ""]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FAILCLOSED
step("Ask for a negative start, an empty span, a span past the end and a span of another function")
val source = "fn observe():\n    return\n"
val digests = [aspect_body_span_digest_v1(source, -1, 5, "observe"),
    aspect_body_span_digest_v1(source, 5, 5, "observe"),
    aspect_body_span_digest_v1(source, 0, source.byte_len() + 1, "observe"),
    aspect_body_span_digest_v1(source, 0, source.byte_len(), "missing")]
step("Every one is the empty digest, which the section builder refuses")
expect(digests).to_equal(["", "", "", ""])
```

</details>

#### an advice id names the declaration slot, not its selector

- Build ids for one slot and for a different module, family, handler and occurrence
- The id is a tagged sha256, repeatable, and each changed part gives another id
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: id.starts_with("sha256:") is true
   - Expected: aspect_decl_advice_id_v1(MODULE, "logical", "trace_submit", 0) equals `id`
   - Expected: other == id is false
   - Expected: edited.advice_id equals `id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FACETS
step("Build ids for one slot and for a different module, family, handler and occurrence")
val id = aspect_decl_advice_id_v1(MODULE, "logical", "trace_submit", 0)
val others = [aspect_decl_advice_id_v1("pkg.other", "logical", "trace_submit", 0),
    aspect_decl_advice_id_v1(MODULE, "mir", "trace_submit", 0),
    aspect_decl_advice_id_v1(MODULE, "logical", "trace_submit", 1),
    aspect_decl_advice_id_v1(MODULE, "logical", "trace_other", 0)]
step("The id is a tagged sha256, repeatable, and each changed part gives another id")
expect(id.starts_with("sha256:")).to_equal(true)
expect(aspect_decl_advice_id_v1(MODULE, "logical", "trace_submit", 0)).to_equal(id)
for other in others:
    expect(other == id).to_equal(false)
val edited = aspect_decl_row_v1(MODULE, resolved("logical", 7, "trace_submit", "pay_view", "static", 3),
    0, "b")
expect(edited.advice_id).to_equal(id)
```

</details>

#### adding an unrelated earlier advice leaves later advice ids unchanged

- Build the section of a module with two advice, then again with an unrelated advice declared before them
- Both existing advice keep their ids although their inventory index moved; the new advice has its own id
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: [after.rows[1].family_inventory_index, before.rows[0].family_inventory_index] equals `[1, 0]`
   - Expected: after.rows[0].advice_id == before.rows[0].advice_id is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FACETS
step("Build the section of a module with two advice, then again with an unrelated advice declared before them")
val digests = {"trace_submit": "b1", "audit_call": "b2", "early_probe": "b3"}
val before = aspect_decl_section_of_semantic_v1(semantic_of([
    resolved("logical", 0, "trace_submit", "submit_view", "static", 0),
    resolved("logical", 1, "audit_call", "audit_view", "static", 0)]), digests).unwrap()
val after = aspect_decl_section_of_semantic_v1(semantic_of([
    resolved("logical", 0, "early_probe", "probe_view", "static", 0),
    resolved("logical", 1, "trace_submit", "submit_view", "static", 0),
    resolved("logical", 2, "audit_call", "audit_view", "static", 0)]), digests).unwrap()
step("Both existing advice keep their ids although their inventory index moved; the new advice has its own id")
expect([after.rows[1].advice_id, after.rows[2].advice_id]).to_equal(
    [before.rows[0].advice_id, before.rows[1].advice_id])
expect([after.rows[1].family_inventory_index, before.rows[0].family_inventory_index]).to_equal([1, 0])
expect(after.rows[0].advice_id == before.rows[0].advice_id).to_equal(false)
```

</details>

#### two declarations of one handler get different advice ids

- Build the section of a module that attaches one handler to two selectors, and to a mir rule of the same name
- Each row has its own id: occurrence 0 per family, then occurrence 1 for the repeated logical handler
   - Exec capture: after_step


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FACETS
step("Build the section of a module that attaches one handler to two selectors, and to a mir rule of the same name")
val section = aspect_decl_section_of_semantic_v1(semantic_of([
    resolved("mir", 0, "trace_submit", "execution(pay*)", "static", 0),
    resolved("logical", 0, "trace_submit", "submit_view", "static", 0),
    resolved("logical", 1, "trace_submit", "pay_view", "static", 0)]), {"trace_submit": "b1"}).unwrap()
step("Each row has its own id: occurrence 0 per family, then occurrence 1 for the repeated logical handler")
expect([section.rows[0].advice_id, section.rows[1].advice_id, section.rows[2].advice_id]).to_equal(
    [aspect_decl_advice_id_v1(MODULE, "mir", "trace_submit", 0),
    aspect_decl_advice_id_v1(MODULE, "logical", "trace_submit", 0),
    aspect_decl_advice_id_v1(MODULE, "logical", "trace_submit", 1)])
```

</details>

#### a resolved handler becomes one row of its family

- Build a row from a static logical handler and from a mir handler in registry mode
- Fields are copied, order is the priority, mode is where the advice runs and activation is the declared weave mode
   - Exec capture: after_step
   - Evidence: execution result verified by 8 expected checks
   - Expected: [logical.readonly, logical.noalloc, logical.bounded_time] equals `[true, true, false]`
   - Expected: logical.signature_digest equals `sha256_text("signature of trace_submit")`
   - Expected: logical.effects_digest equals `sha256_text("effects of trace_submit")`
   - Expected: logical.body_digest equals `body-1`
   - Expected: [dynamic.family, dynamic.form, dynamic.mode, dynamic.activation] equals `["mir", "after", "after", "registry"]`
   - Expected: [dynamic.family_inventory_index, dynamic.order] equals `[2, 9]`
   - Expected: dynamic.scope_id equals `logical.scope_id`
   - Expected: dynamic.selector_id == logical.selector_id is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-CODEC
step("Build a row from a static logical handler and from a mir handler in registry mode")
val logical = aspect_decl_row_v1(MODULE, logical_handler(), 0, "body-1")
val dynamic = aspect_decl_row_v1(MODULE, resolved("mir", 2, "audit_call", "execution(audit*)", "registry", 9), 0, "body-2")
step("Fields are copied, order is the priority, mode is where the advice runs and activation is the declared weave mode")
expect([logical.family, logical.handler, logical.form, logical.mode, logical.activation,
    logical.selector]).to_equal(["logical", "trace_submit", "forward", "before", "static", "submit_view"])
expect([logical.readonly, logical.noalloc, logical.bounded_time]).to_equal([true, true, false])
expect(logical.signature_digest).to_equal(sha256_text("signature of trace_submit"))
expect(logical.effects_digest).to_equal(sha256_text("effects of trace_submit"))
expect(logical.body_digest).to_equal("body-1")
expect([dynamic.family, dynamic.form, dynamic.mode, dynamic.activation]).to_equal(["mir", "after", "after", "registry"])
expect([dynamic.family_inventory_index, dynamic.order]).to_equal([2, 9])
expect(dynamic.scope_id).to_equal(logical.scope_id)
expect(dynamic.selector_id == logical.selector_id).to_equal(false)
```

</details>

#### an advice body edit changes only the body facet

- Build the same declaration with two body digests, then with another selector
- The body edit keeps the row digest; the selector edit changes the row digest and the selector id
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: aspect_decl_row_digest_v1(body_edit) equals `aspect_decl_row_digest_v1(before)`
   - Expected: body_edit.body_digest == before.body_digest is false
   - Expected: aspect_decl_row_digest_v1(selector_edit) == aspect_decl_row_digest_v1(before) is false
   - Expected: selector_edit.selector_id == before.selector_id is false
   - Expected: selector_edit.body_digest equals `before.body_digest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FACETS
step("Build the same declaration with two body digests, then with another selector")
val before = aspect_decl_row_v1(MODULE, logical_handler(), 0, "body-1")
val body_edit = aspect_decl_row_v1(MODULE, logical_handler(), 0, "body-2")
val selector_edit = aspect_decl_row_v1(MODULE,
    resolved("logical", 0, "trace_submit", "pay_view", "static", 0), 0, "body-1")
step("The body edit keeps the row digest; the selector edit changes the row digest and the selector id")
expect(aspect_decl_row_digest_v1(body_edit)).to_equal(aspect_decl_row_digest_v1(before))
expect(body_edit.body_digest == before.body_digest).to_equal(false)
expect(aspect_decl_row_digest_v1(selector_edit) == aspect_decl_row_digest_v1(before)).to_equal(false)
expect(selector_edit.selector_id == before.selector_id).to_equal(false)
expect(selector_edit.body_digest).to_equal(before.body_digest)
```

</details>

### aspect-decl section

#### a module's capture becomes one section with a row per declaration

- Build the section of a module that declares one mir and one logical advice
- The header carries the module, schema and leaf digest; rows keep declaration order
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: [section.rows[0].handler, section.rows[1].handler] equals `["audit_call", "trace_submit"]`
   - Expected: aspect_decl_section_of_semantic_v1(semantic_of([]), {}).unwrap().rows.len() equals `0)  # oracle: no declaration, no row`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-CODEC
step("Build the section of a module that declares one mir and one logical advice")
val section = both_families()
step("The header carries the module, schema and leaf digest; rows keep declaration order")
expect([section.module_identity, section.coverage_schema, section.leaf_digest]).to_equal(
    [MODULE, "current-parser-aop/v1", sha256_text("interface")])
expect([section.rows[0].handler, section.rows[1].handler]).to_equal(["audit_call", "trace_submit"])
expect(aspect_decl_section_of_semantic_v1(semantic_of([]), {}).unwrap().rows.len()).to_equal(0)  # oracle: no declaration, no row
```

</details>

#### a handler without a body digest is an error

- Build a section when the handler is absent from the digest map, then when its digest is empty
- Both are the same error; no row with an empty facet is produced
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: absent.unwrap_err() equals `advice-body-unavailable`
   - Expected: empty.unwrap_err() equals `advice-body-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FAILCLOSED
step("Build a section when the handler is absent from the digest map, then when its digest is empty")
val absent = aspect_decl_section_of_semantic_v1(semantic_of([logical_handler()]), {})
val empty = aspect_decl_section_of_semantic_v1(semantic_of([logical_handler()]), {"trace_submit": ""})
step("Both are the same error; no row with an empty facet is produced")
expect(absent.unwrap_err()).to_equal("advice-body-unavailable")
expect(empty.unwrap_err()).to_equal("advice-body-unavailable")
```

</details>

#### both families round trip through the section text

- Encode a section with a mir row of negative order and a logical row, then decode it
- Status is ok and every field of every row equals the encoded one
   - Exec capture: after_step
   - Evidence: execution result verified by 6 expected checks
   - Expected: outcome(decoded) equals `ok::2`
   - Expected: aspect_decl_row_digest_v1(got) equals `aspect_decl_row_digest_v1(want)`
   - Expected: got.body_digest equals `want.body_digest`
   - Expected: decoded.section.rows[0].order equals `-5)  # oracle: the mir fixture priority`
   - Expected: decoded.section.rows[0].family equals `mir`
   - Expected: decoded.section.rows[1].family equals `logical`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-CODEC
step("Encode a section with a mir row of negative order and a logical row, then decode it")
val section = both_families()
val decoded = aspect_decl_section_decode_v1(encoded_both())
step("Status is ok and every field of every row equals the encoded one")
expect(outcome(decoded)).to_equal("ok::2")
expect([decoded.section.module_identity, decoded.section.coverage_schema,
    decoded.section.leaf_digest]).to_equal([section.module_identity, section.coverage_schema,
    section.leaf_digest])
for i in 0..2:
    val want = section.rows[i]
    val got = decoded.section.rows[i]
    expect(aspect_decl_row_digest_v1(got)).to_equal(aspect_decl_row_digest_v1(want))
    expect(got.body_digest).to_equal(want.body_digest)
    expect([got.readonly, got.noalloc, got.bounded_time]).to_equal(
        [want.readonly, want.noalloc, want.bounded_time])
expect(decoded.section.rows[0].order).to_equal(-5)  # oracle: the mir fixture priority
expect(decoded.section.rows[0].family).to_equal("mir")
expect(decoded.section.rows[1].family).to_equal("logical")
```

</details>

#### a non-ASCII selector round trips unchanged

- Encode and decode a section whose selector and handler names are not ASCII
- The decoded row has the same handler and selector
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: decoded.status equals `ASPECT_SECTION_OK_V1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-CODEC
step("Encode and decode a section whose selector and handler names are not ASCII")
val handler = resolved("logical", 0, "추적_제출", "within(결제.*)", "static", 0)
val section = aspect_decl_section_of_semantic_v1(semantic_of([handler]), {"추적_제출": "b"}).unwrap()
val decoded = aspect_decl_section_decode_v1(aspect_decl_section_encode_v1(section).unwrap())
step("The decoded row has the same handler and selector")
expect(decoded.status).to_equal(ASPECT_SECTION_OK_V1)
expect([decoded.section.rows[0].handler, decoded.section.rows[0].selector]).to_equal(
    ["추적_제출", "within(결제.*)"])
```

</details>

#### encoding refuses every over-limit section

- Encode 1025 rows, a module name over 64 KiB, a selector over 64 KiB, and 17 rows of 64 KiB selectors
- Each is refused with the limit it broke; a row at exactly the field limit still encodes
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: errors equals `["row-limit", "field-limit", "field-limit", "section-limit"]`
   - Expected: aspect_decl_section_encode_v1(AspectDeclSectionV1(..base, rows: [wide_row])).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FAILCLOSED
step("Encode 1025 rows, a module name over 64 KiB, a selector over 64 KiB, and 17 rows of 64 KiB selectors")
val row = aspect_decl_row_v1(MODULE, logical_handler(), 0, "b")
var many: [AspectDeclRowV1] = []
for i in 0..1025:
    many.push(row)
val wide = repeated("x", ASPECT_DECL_SECTION_MAX_FIELD_BYTES_V1)
val wide_row = aspect_decl_row_v1(MODULE, resolved("logical", 0, "trace_submit", wide, "static", 0), 0, "b")
var heavy: [AspectDeclRowV1] = []
for i in 0..17:
    heavy.push(wide_row)
val base = both_families()
val errors = [
    aspect_decl_section_encode_v1(AspectDeclSectionV1(..base, rows: many)).unwrap_err(),
    aspect_decl_section_encode_v1(AspectDeclSectionV1(..base, module_identity: wide + "x")).unwrap_err(),
    aspect_decl_section_encode_v1(AspectDeclSectionV1(..base, rows: [AspectDeclRowV1(..row, selector: wide + "x")])).unwrap_err(),
    aspect_decl_section_encode_v1(AspectDeclSectionV1(..base, rows: heavy)).unwrap_err()]
step("Each is refused with the limit it broke; a row at exactly the field limit still encodes")
expect(errors).to_equal(["row-limit", "field-limit", "field-limit", "section-limit"])
expect(aspect_decl_section_encode_v1(AspectDeclSectionV1(..base, rows: [wide_row])).is_ok()).to_equal(true)
```

</details>

### aspect-decl section decode

#### a truncated section is rejected

- Cut a valid section in the middle of a frame, and cut it to its first three values
- The first is a malformed frame, the second a truncated section; neither yields rows
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: outcome(mid_frame) equals `reject:malformed-frame:0`
   - Expected: outcome(three) equals `reject:truncated-section:0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FAILCLOSED
step("Cut a valid section in the middle of a frame, and cut it to its first three values")
val wire = encoded_both()
val mid_frame = aspect_decl_section_decode_v1(wire.substring(0, wire.byte_len() - 10))
val three = aspect_decl_section_decode_v1(sealed([ASPECT_DECL_SECTION_MAGIC_V1, MODULE]))
step("The first is a malformed frame, the second a truncated section; neither yields rows")
expect(outcome(mid_frame)).to_equal("reject:malformed-frame:0")
expect(outcome(three)).to_equal("reject:truncated-section:0")
```

</details>

#### a section over the byte limit is rejected before it is read

- Decode a text one byte over the section limit
- It is rejected for its size
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: outcome(result) equals `reject:section-limit:0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FAILCLOSED
step("Decode a text one byte over the section limit")
val result = aspect_decl_section_decode_v1(repeated("x", ASPECT_DECL_SECTION_MAX_BYTES_V1 + 1))
step("It is rejected for its size")
expect(outcome(result)).to_equal("reject:section-limit:0")
```

</details>

#### a foreign magic or a changed byte is rejected

- Decode a sealed section with another magic, then a valid section with one value byte changed
- The first is a bad magic, the second a seal mismatch
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: outcome(foreign) equals `reject:bad-magic:0`
   - Expected: outcome(tampered) equals `reject:seal-mismatch:0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FAILCLOSED
step("Decode a sealed section with another magic, then a valid section with one value byte changed")
val foreign = aspect_decl_section_decode_v1(sealed(["aspect-decl/v9", MODULE, "s", "l", "0", "x"]))
val tampered = aspect_decl_section_decode_v1(encoded_both().replace("trace_submit", "trace_submix"))
step("The first is a bad magic, the second a seal mismatch")
expect(outcome(foreign)).to_equal("reject:bad-magic:0")
expect(outcome(tampered)).to_equal("reject:seal-mismatch:0")
```

</details>

#### an unknown digest algorithm is a miss, not a reject

- Replace the sha256 seal of a valid section by a seal of an algorithm this reader does not know
- The section is a miss with no rows: the reader recomputes instead of trusting it
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: outcome(unknown) equals `miss:unknown-digest-algorithm:0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FAILCLOSED
step("Replace the sha256 seal of a valid section by a seal of an algorithm this reader does not know")
val wire = encoded_both()
val body = wire.substring(aspect_section_frame_v1(aspect_section_seal_v1("")).byte_len(), wire.byte_len())
val unknown = aspect_decl_section_decode_v1(aspect_section_frame_v1("sha9:" + sha256_text(body)) + body)
step("The section is a miss with no rows: the reader recomputes instead of trusting it")
expect(outcome(unknown)).to_equal("miss:unknown-digest-algorithm:0")
```

</details>

#### a bad or over-limit row count is rejected

- Decode sealed sections whose row count is not a number, is 1025, or promises a row that is absent
- Each is rejected with its own reason
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: outcome(not_number) equals `reject:bad-row-count:0`
   - Expected: outcome(over) equals `reject:row-limit:0`
   - Expected: outcome(absent) equals `reject:truncated-section:0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FAILCLOSED
step("Decode sealed sections whose row count is not a number, is 1025, or promises a row that is absent")
val not_number = aspect_decl_section_decode_v1(sealed(section_values("x", "0", [])))
val over = aspect_decl_section_decode_v1(sealed(section_values("1025", "0", [])))
val absent = aspect_decl_section_decode_v1(sealed([ASPECT_DECL_SECTION_MAGIC_V1, MODULE, "s", "l", "1"]))
step("Each is rejected with its own reason")
expect(outcome(not_number)).to_equal("reject:bad-row-count:0")
expect(outcome(over)).to_equal("reject:row-limit:0")
expect(outcome(absent)).to_equal("reject:truncated-section:0")
```

</details>

#### a row that promises more fields than it has is rejected

- Decode a row whose pair count is not a number, and one whose pair count overruns the section
- Both are a truncated row
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: outcome(not_number) equals `reject:truncated-row:0`
   - Expected: outcome(overrun) equals `reject:truncated-row:0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FAILCLOSED
step("Decode a row whose pair count is not a number, and one whose pair count overruns the section")
val not_number = aspect_decl_section_decode_v1(sealed(section_values("1", "x", valid_pairs())))
val overrun = aspect_decl_section_decode_v1(sealed(section_values("1", "18", valid_pairs())))
step("Both are a truncated row")
expect(outcome(not_number)).to_equal("reject:truncated-row:0")
expect(outcome(overrun)).to_equal("reject:truncated-row:0")
```

</details>

#### values after the last row are rejected

- Append one more value after the only row of a sealed section
- The section is rejected for trailing data; the same section without it decodes
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: outcome(aspect_decl_section_decode_v1(sealed(values))) equals `reject:trailing-data:0`
   - Expected: outcome(one_row(valid_pairs())) equals `ok::1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FAILCLOSED
step("Append one more value after the only row of a sealed section")
var values = section_values("1", "17", valid_pairs())
values.push("extra")
step("The section is rejected for trailing data; the same section without it decodes")
expect(outcome(aspect_decl_section_decode_v1(sealed(values)))).to_equal("reject:trailing-data:0")
expect(outcome(one_row(valid_pairs()))).to_equal("ok::1")
```

</details>

#### an unknown optional field is ignored

- Add a `?`-prefixed field this reader does not know to a valid row, twice
- The row decodes with its known fields unchanged
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: outcome(result) equals `ok::1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-CODEC
step("Add a `?`-prefixed field this reader does not know to a valid row, twice")
var pairs = valid_pairs()
for extra in ["?future_hint", "anything", "?future_hint", "again"]:
    pairs.push(extra)
val result = one_row(pairs)
step("The row decodes with its known fields unchanged")
expect(outcome(result)).to_equal("ok::1")
expect([result.section.rows[0].handler, result.section.rows[0].selector]).to_equal(
    ["trace_submit", "submit_view"])
expect([result.section.rows[0].readonly, result.section.rows[0].noalloc,
    result.section.rows[0].bounded_time]).to_equal([true, false, true])
```

</details>

#### an unknown mandatory field is rejected

- Add a field without the `?` prefix, repeat a known field, and drop a known field
- Unknown mandatory, duplicate and missing fields each reject the section
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: outcome(one_row(unknown)) equals `reject:unknown-mandatory-field:0`
   - Expected: outcome(one_row(duplicate)) equals `reject:duplicate-field:0`
   - Expected: outcome(one_row(without_key(valid_pairs(), "effects"))) equals `reject:missing-field:0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FAILCLOSED
step("Add a field without the `?` prefix, repeat a known field, and drop a known field")
var unknown = valid_pairs()
unknown.push("around_guard")
unknown.push("1")
var duplicate = valid_pairs()
duplicate.push("handler")
duplicate.push("other")
step("Unknown mandatory, duplicate and missing fields each reject the section")
expect(outcome(one_row(unknown))).to_equal("reject:unknown-mandatory-field:0")
expect(outcome(one_row(duplicate))).to_equal("reject:duplicate-field:0")
expect(outcome(one_row(without_key(valid_pairs(), "effects")))).to_equal("reject:missing-field:0")
```

</details>

#### a row with a bad number or flag is rejected

- Decode rows with a non-numeric index, a negative index, a bad order, a bad negative order and a flag of 2
- Each is rejected; a negative order alone is accepted
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: verdicts equals `["reject:bad-number:0", "reject:bad-number:0", "reject:bad-number:0",`
   - Expected: negative.section.rows[0].order equals `-12)  # oracle: the order written into the row`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FAILCLOSED
step("Decode rows with a non-numeric index, a negative index, a bad order, a bad negative order and a flag of 2")
val verdicts = [outcome(one_row(with_value(valid_pairs(), "index", "x"))),
    outcome(one_row(with_value(valid_pairs(), "index", "-1"))),
    outcome(one_row(with_value(valid_pairs(), "order", "1.5"))),
    outcome(one_row(with_value(valid_pairs(), "order", "-x"))),
    outcome(one_row(with_value(valid_pairs(), "bounded_time", "2")))]
step("Each is rejected; a negative order alone is accepted")
expect(verdicts).to_equal(["reject:bad-number:0", "reject:bad-number:0", "reject:bad-number:0",
    "reject:bad-number:0", "reject:bad-flag:0"])
val negative = one_row(with_value(valid_pairs(), "order", "-12"))
expect(negative.section.rows[0].order).to_equal(-12)  # oracle: the order written into the row
```

</details>

### aspect-decl TLDR entry

#### a module TLDR carries exactly one section

- Render the entry among other TLDR sections, parse the TLDR text back, and read the section
- The TLDR parser admits the `aspect-decl` kind and the section decodes with both rows
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: entry.starts_with("aspect-decl|") is true
   - Expected: consumed equals `wire.byte_len()`
   - Expected: outcome(found) equals `ok::2`
   - Expected: found.section.rows[1].handler equals `trace_submit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-CODEC
step("Render the entry among other TLDR sections, parse the TLDR text back, and read the section")
val entry = aspect_decl_section_entry_v1(both_families()).unwrap()
val wire = module_tldr_sections_render_v1(["const|val LIMIT: i64 = 42", entry])
val (entries, consumed) = module_tldr_sections_parse_v1(wire)
val found = aspect_decl_section_of_entries_v1(entries)
step("The TLDR parser admits the `aspect-decl` kind and the section decodes with both rows")
expect(entry.starts_with("aspect-decl|")).to_equal(true)
expect(consumed).to_equal(wire.byte_len())
expect(outcome(found)).to_equal("ok::2")
expect(found.section.rows[1].handler).to_equal("trace_submit")
```

</details>

#### a TLDR without the section is a miss and a TLDR with two is rejected

- Read the section from entries that have none, and from entries that have it twice
- Absence is a miss, duplication is a reject, and an over-limit section has no entry at all
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: outcome(none) equals `miss:section-absent:0`
   - Expected: outcome(twice) equals `reject:duplicate-section:0`
   - Expected: aspect_decl_section_entry_v1(AspectDeclSectionV1(..both_families(), rows: many)).unwrap_err() equals `row-limit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW1-FAILCLOSED
step("Read the section from entries that have none, and from entries that have it twice")
val entry = aspect_decl_section_entry_v1(both_families()).unwrap()
val none = aspect_decl_section_of_entries_v1(["const|val LIMIT: i64 = 42"])
val twice = aspect_decl_section_of_entries_v1([entry, "const|val LIMIT: i64 = 42", entry])
step("Absence is a miss, duplication is a reject, and an over-limit section has no entry at all")
expect(outcome(none)).to_equal("miss:section-absent:0")
expect(outcome(twice)).to_equal("reject:duplicate-section:0")
var many: [AspectDeclRowV1] = []
for i in 0..1025:
    many.push(both_families().rows[0])
expect(aspect_decl_section_entry_v1(AspectDeclSectionV1(..both_families(), rows: many)).unwrap_err()).to_equal("row-limit")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-ASPECT-AW1-CODEC`
- `REQ-ASPECT-AW1-FAILCLOSED`
- `REQ-ASPECT-AW1-FACETS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `efb3adfe13150f7089980c0b510442255bbf6f82197fb63ba72096c277eb6821`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `efb3adfe13150f7089980c0b510442255bbf6f82197fb63ba72096c277eb6821`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `efb3adfe13150f7089980c0b510442255bbf6f82197fb63ba72096c277eb6821`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: 01_unit/compiler/aop/aspect_decl_section_v1_spec.spl
mirror: doc/06_spec/01_unit/compiler/aop/aspect_decl_section_v1_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/aop/aspect_decl_section_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/aop/aspect_decl_section_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
