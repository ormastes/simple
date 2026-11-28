# `join-point|`: the join points a module publishes in its TLDR

> Purpose: document and pin

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# `join-point|`: the join points a module publishes in its TLDR

Purpose: document and pin

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/aop/join_point_section_v2_spec.spl` |
| Updated | 2026-11-28 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

Purpose: document and pin
`src/compiler/00.common/cache_contract/join_point_section_v2.spl` (aspect plan
stage AW-2). A module writes its forward join points into its own TLDR as
`JoinPointFactV2` rows. A directory's join-point facts are then built from its
members' sections, and a directory's aspect root is computed from its members'
aspect leaf digests, without opening any member's HIR.

Audience: compiler engineers who build weave plans, directory facts or the
incremental planner on top of these rows, and reviewers checking that a
missing or damaged section can only make facts incomplete, never wrong.

## What JoinPointFactV2 adds

| Field | V1 | V2 |
|-------|----|----|
| id, kind, symbol, attrs, owner file | yes | same values |
| `base_body_digest` | field exists, production leaves it empty | always present |
| `signature_digest` | absent | always present |
| `guard_ids` | absent | ids of the static guards evaluated in the owning file |

The builder refuses a row that lacks a signature or body digest, so a section
never holds a half-filled fact. Non-exported functions are rows like any
other: advice applies to private forwarders too.

## Operator workflow

1. Run `bin/simple test test/01_unit/compiler/aop/join_point_section_v2_spec.spl`
   from the repository root. No fixture file and no host fact is read.
2. Measure coverage with
   `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=<f> <seed> run <this spec>`
   (doc/07_guide/infra/testing/coverage.md).

## Completeness of directory facts

`directory_join_point_facts_of_sections_v2` returns `complete = true` only
when every member file has exactly one section written for the requested guard
profile. A section of a file outside the directory, a second section of one
member, or a section of another profile is left out and makes the facts
incomplete. Incomplete facts are a cache miss for every consumer.

## Aspect root

`aspect_root_digest_v1` hashes the members' leaf digests and the child
directories' roots as sorted lists. The leaf digest holds no advice body, so
an advice body edit moves no root.

## Lifecycle

Research: doc/01_research/local/dir_tldr_aspect.md
Plan: doc/03_plan/compiler/aspect_cache/aspect_tldr_async_trace_plan.md (AW-2)
Architecture: doc/04_architecture/compiler/aspect_dynload/typed_facet_pipeline_2026-08-22.md
Design: doc/05_design/compiler/cache/aspect_tldr_async_trace.md (sections 3 and 5, gap G15)

## Decision inventory (MC/DC)

Function names refer to `join_point_section_v2.spl`.

| Function | Decision | Covering scenario |
|----------|----------|-------------------|
| `_sorted_texts_v2` | insertion stops at the front or at a smaller value | "a module's join points become sorted V2 facts" |
| `_guard_ids_v2` | guard has a digest; digest already listed | same |
| `join_point_section_v2` | key or file empty; symbol or kind empty; signature empty; body empty; insertion position; duplicate id | "a row without an owner, symbol, signature or body digest is refused", "two rows of one symbol are refused" |
| `join_point_section_encode_v2` | point limit; guard limit; field limit; section limit | "encoding refuses every over-limit section" |
| `_point_decode_v2` | known key; duplicate; optional `?` key; missing key; attrs unreadable | "an unknown optional field is ignored", "a row with an unknown, repeated, missing or unreadable field is rejected" |
| `join_point_section_decode_v2` | size; framing; fewer than seven values; magic; seal miss; seal reject; guard count unreadable or over limit; guards overrun; guard flag; point count unreadable or over limit; rows run out; pair count unreadable or overrunning; row error; trailing values; builder rule | the `decode` scenarios |
| `join_point_section_of_entries_v2` | entry has the kind prefix; none; more than one | "a module TLDR carries exactly one section" |
| `directory_join_point_facts_of_sections_v2` | non-member; second section; other profile; member without section | the `directory facts` scenarios |

Exclusions: none.

## Compatibility and limitations

`guard_ids` has file granularity: every fact of a file lists all guards
evaluated in that file, not only the guards that enclose its function.
The directory facts are `DirectoryJoinPointFactsV1`, so existing shard and
planner code reads them unchanged; `signature_digest` and `guard_ids` are read
from the section rows.

## Scenarios

### join_point_section_v2

#### a module's join points become sorted V2 facts

- Build a section from three rows given out of order, with unsorted attributes and four guards
- Rows are sorted by id; each fact has sorted attributes, both digests and the file's guard ids
   - Exec capture: after_step
   - Evidence: execution result verified by 10 expected checks
   - Expected: ids(section.points) equals `["pay_a::audit_view", "pay_a::pay_view", "pay_a::submit_view"]`
   - Expected: [last.kind, last.symbol, last.owner_file] equals `["forward", "submit_view", "pay/pay_a.spl"]`
   - Expected: last.attrs equals `["logged", "traced"]`
   - Expected: last.signature_digest equals `sha256_text("signature of submit_view")`
   - Expected: last.base_body_digest equals `sha256_text("body of submit_view")`
   - Expected: last.guard_ids.len() equals `want_ids.len()`
   - Expected: last.guard_ids contains `want_ids[0]) and last.guard_ids`
   - Expected: last.guard_ids[0] < last.guard_ids[1] is true
   - Expected: first.guard_ids equals `last.guard_ids`
   - Expected: section.guards.len() equals `guards.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-FACT
step("Build a section from three rows given out of order, with unsorted attributes and four guards")
val guards = [guard("when", "b", true, true), guard("cfg", "a", true, false),
    guard("when", "b", true, true), guard("weird", "c", false, false)]
val section = join_point_section_v2("pay_a", "pay/pay_a.spl", PROFILE, guards,
    [row("submit_view", ["traced", "logged"]), row("audit_view", []), row("pay_view", ["x"])]).unwrap()
val first = section.points[0]
val last = section.points[2]
step("Rows are sorted by id; each fact has sorted attributes, both digests and the file's guard ids")
expect(ids(section.points)).to_equal(["pay_a::audit_view", "pay_a::pay_view", "pay_a::submit_view"])
expect([last.kind, last.symbol, last.owner_file]).to_equal(["forward", "submit_view", "pay/pay_a.spl"])
expect(last.attrs).to_equal(["logged", "traced"])
expect(last.signature_digest).to_equal(sha256_text("signature of submit_view"))
expect(last.base_body_digest).to_equal(sha256_text("body of submit_view"))
val want_ids = [guard_id_v1("when", "b").digest, guard_id_v1("cfg", "a").digest]
expect(last.guard_ids.len()).to_equal(want_ids.len())
expect(last.guard_ids.contains(want_ids[0]) and last.guard_ids.contains(want_ids[1])).to_equal(true)
expect(last.guard_ids[0] < last.guard_ids[1]).to_equal(true)
expect(first.guard_ids).to_equal(last.guard_ids)
expect(section.guards.len()).to_equal(guards.len())
```

</details>

#### a row without an owner, symbol, signature or body digest is refused

- Build sections with an empty module key, file, symbol, kind, signature digest and body digest
- Each is refused with its own reason, so a section never holds a half-filled fact
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: errors equals `["join-point-owner-missing", "join-point-owner-missing",`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-FAILCLOSED
step("Build sections with an empty module key, file, symbol, kind, signature digest and body digest")
val good = row("submit_view", [])
val errors = [error_of("", "pay/pay_a.spl", good), error_of("pay_a", "", good),
    error_of("pay_a", "pay/pay_a.spl", JoinPointRowInputV2(..good, symbol: "")),
    error_of("pay_a", "pay/pay_a.spl", JoinPointRowInputV2(..good, kind: "")),
    error_of("pay_a", "pay/pay_a.spl", JoinPointRowInputV2(..good, signature_digest: "")),
    error_of("pay_a", "pay/pay_a.spl", JoinPointRowInputV2(..good, base_body_digest: ""))]
step("Each is refused with its own reason, so a section never holds a half-filled fact")
expect(errors).to_equal(["join-point-owner-missing", "join-point-owner-missing",
    "join-point-symbol-missing", "join-point-symbol-missing",
    "join-point-signature-unavailable", "join-point-body-unavailable"])
```

</details>

#### two rows of one symbol are refused

- Build a section whose rows name `submit_view` twice, among other rows
- The section is refused: a join-point id is unique in its module
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: result.unwrap_err() equals `join-point-duplicate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-FAILCLOSED
step("Build a section whose rows name `submit_view` twice, among other rows")
val result = join_point_section_v2("pay_a", "pay/pay_a.spl", PROFILE, [],
    [row("submit_view", []), row("audit_view", []), row("submit_view", ["logged"])])
step("The section is refused: a join-point id is unique in its module")
expect(result.unwrap_err()).to_equal("join-point-duplicate")
```

</details>

#### a V2 fact projects to the V1 fact with a real body digest

- Project the facts of a built section to JoinPointFactV1
- Every shared field is copied and the body digest is not empty
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: v1.attrs equals `["logged"]`
   - Expected: v1.base_body_digest equals `sha256_text("body of submit_view")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-FACT
step("Project the facts of a built section to JoinPointFactV1")
val point = section_a().points[1]
val v1 = join_point_fact_v1_of_v2(point)
step("Every shared field is copied and the body digest is not empty")
expect([v1.id, v1.kind, v1.symbol, v1.owner_file]).to_equal(
    ["pay_a::submit_view", "forward", "submit_view", "pay/pay_a.spl"])
expect(v1.attrs).to_equal(["logged"])
expect(v1.base_body_digest).to_equal(sha256_text("body of submit_view"))
```

</details>

### join-point section text

#### a section round trips with its guards and rows

- Encode a section with an active, an inactive and an unevaluable guard and a non-ASCII attribute, then decode it
- Status is ok; header, guards and every field of every row equal the encoded ones
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: outcome(decoded) equals `ok::2`
   - Expected: got.attrs equals `want.attrs`
   - Expected: got.guard_ids equals `want.guard_ids`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-CODEC
step("Encode a section with an active, an inactive and an unevaluable guard and a non-ASCII attribute, then decode it")
val guards = [guard("when", "1:when:os=\"linux\"", true, true), guard("cfg", "4:cfg:x", true, false),
    guard("when", "unevaluable:no atom", false, false)]
val section = join_point_section_v2("결제_a", "pay/결제_a.spl", PROFILE, guards,
    [row("submit_view", ["기록", "logged"]), row("_private_view", [])]).unwrap()
val decoded = join_point_section_decode_v2(join_point_section_encode_v2(section).unwrap())
step("Status is ok; header, guards and every field of every row equal the encoded ones")
expect(outcome(decoded)).to_equal("ok::2")
expect([decoded.section.module_key, decoded.section.owner_file, decoded.section.guard_profile]).to_equal(
    ["결제_a", "pay/결제_a.spl", PROFILE])
for i in 0..3:
    expect([decoded.section.guards[i].guard.kind, decoded.section.guards[i].guard.canonical_expr,
        decoded.section.guards[i].guard.digest]).to_equal([guards[i].guard.kind,
        guards[i].guard.canonical_expr, guards[i].guard.digest])
    expect([decoded.section.guards[i].evaluable, decoded.section.guards[i].active]).to_equal(
        [guards[i].evaluable, guards[i].active])
for i in 0..2:
    val want = section.points[i]
    val got = decoded.section.points[i]
    expect([got.id, got.kind, got.symbol, got.owner_file, got.signature_digest,
        got.base_body_digest]).to_equal([want.id, want.kind, want.symbol, want.owner_file,
        want.signature_digest, want.base_body_digest])
    expect(got.attrs).to_equal(want.attrs)
    expect(got.guard_ids).to_equal(want.guard_ids)
```

</details>

#### encoding refuses every over-limit section

- Encode 4097 rows, 1025 guards, a symbol over 64 KiB, and 71 rows of 60 KiB symbols
- Each is refused with the limit it broke; one 60 KiB row alone still encodes
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: errors equals `["point-limit", "guard-limit", "field-limit", "section-limit"]`
   - Expected: join_point_section_encode_v2(JoinPointSectionV2(..base, points: [heavy_point])).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-FAILCLOSED
step("Encode 4097 rows, 1025 guards, a symbol over 64 KiB, and 71 rows of 60 KiB symbols")
val base = section_a()
val point = base.points[0]
var many_points: [JoinPointFactV2] = []
for i in 0..4097:
    many_points.push(point)
var many_guards: [GuardEvalV1] = []
for i in 0..1025:
    many_guards.push(guards_of_a()[0])
val wide = repeated("x", JOIN_POINT_SECTION_MAX_FIELD_BYTES_V2 + 1)
val heavy_point = JoinPointFactV2(..point, symbol: repeated("y", 60000))
var heavy: [JoinPointFactV2] = []
for i in 0..71:
    heavy.push(heavy_point)
val errors = [
    join_point_section_encode_v2(JoinPointSectionV2(..base, points: many_points)).unwrap_err(),
    join_point_section_encode_v2(JoinPointSectionV2(..base, guards: many_guards)).unwrap_err(),
    join_point_section_encode_v2(JoinPointSectionV2(..base, points: [JoinPointFactV2(..point, symbol: wide)])).unwrap_err(),
    join_point_section_encode_v2(JoinPointSectionV2(..base, points: heavy)).unwrap_err()]
step("Each is refused with the limit it broke; one 60 KiB row alone still encodes")
expect(errors).to_equal(["point-limit", "guard-limit", "field-limit", "section-limit"])
expect(join_point_section_encode_v2(JoinPointSectionV2(..base, points: [heavy_point])).is_ok()).to_equal(true)
```

</details>

### join-point section decode

#### a truncated or oversized section is rejected

- Cut a valid section mid-frame, cut it to its header start, and decode a text over the byte limit
- They are a malformed frame, a truncated section and a size reject; none yields rows
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: verdicts equals `["reject:malformed-frame:0", "reject:truncated-section:0",`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-FAILCLOSED
step("Cut a valid section mid-frame, cut it to its header start, and decode a text over the byte limit")
val wire = join_point_section_encode_v2(section_a()).unwrap()
val verdicts = [outcome(join_point_section_decode_v2(wire.substring(0, wire.byte_len() - 9))),
    outcome(join_point_section_decode_v2(sealed([JOIN_POINT_SECTION_MAGIC_V2, "pay_a", "f", PROFILE]))),
    outcome(join_point_section_decode_v2(repeated("x", JOIN_POINT_SECTION_MAX_BYTES_V2 + 1)))]
step("They are a malformed frame, a truncated section and a size reject; none yields rows")
expect(verdicts).to_equal(["reject:malformed-frame:0", "reject:truncated-section:0",
    "reject:section-limit:0"])
```

</details>

#### a foreign magic or a changed byte is rejected and an unknown seal algorithm is a miss

- Decode a sealed section with another magic, a valid one with a changed value, and one with a foreign seal
- Bad magic and seal mismatch are rejects; the unknown algorithm is a miss, so the reader recomputes
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: verdicts equals `["reject:bad-magic:0", "reject:seal-mismatch:0",`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-FAILCLOSED
step("Decode a sealed section with another magic, a valid one with a changed value, and one with a foreign seal")
val wire = join_point_section_encode_v2(section_a()).unwrap()
val body = wire.substring(aspect_section_frame_v1(aspect_section_seal_v1("")).byte_len(), wire.byte_len())
val verdicts = [
    outcome(join_point_section_decode_v2(sealed(["join-point/v9", "pay_a", "f", PROFILE, "0", "0"]))),
    outcome(join_point_section_decode_v2(wire.replace("submit_view", "submit_vieW"))),
    outcome(join_point_section_decode_v2(aspect_section_frame_v1("sha9:" + sha256_text(body)) + body))]
step("Bad magic and seal mismatch are rejects; the unknown algorithm is a miss, so the reader recomputes")
expect(verdicts).to_equal(["reject:bad-magic:0", "reject:seal-mismatch:0",
    "miss:unknown-digest-algorithm:0"])
```

</details>

#### a bad guard block is rejected

- Decode sections with an unreadable guard count, 1025 guards, a guard that is cut off, and guard flags of 2
- Count and overrun rejects name the limit or the truncation; bad flags are bad flags; the valid block decodes
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: verdicts equals `["reject:guard-limit:0", "reject:guard-limit:0",`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-FAILCLOSED
step("Decode sections with an unreadable guard count, 1025 guards, a guard that is cut off, and guard flags of 2")
val g = ["when", "expr", "sha256:" + sha256_text("g")]
val verdicts = [
    outcome(join_point_section_decode_v2(sealed(joined([head("x"), ["0"]])))),
    outcome(join_point_section_decode_v2(sealed(joined([head("1025"), ["0"]])))),
    outcome(join_point_section_decode_v2(sealed(joined([head("1"), g, ["1", "0"]])))),
    outcome(join_point_section_decode_v2(sealed(joined([head("1"), g, ["2", "0"], ["0"]])))),
    outcome(join_point_section_decode_v2(sealed(joined([head("1"), g, ["1", "2"], ["0"]])))),
    outcome(join_point_section_decode_v2(sealed(joined([head("1"), g, ["1", "0"], ["0"]]))))]
step("Count and overrun rejects name the limit or the truncation; bad flags are bad flags; the valid block decodes")
expect(verdicts).to_equal(["reject:guard-limit:0", "reject:guard-limit:0",
    "reject:truncated-section:0", "reject:bad-flag:0", "reject:bad-flag:0", "ok::0"])
```

</details>

#### a bad point count or a cut-off row is rejected

- Decode sections with an unreadable point count, 4097 points, a promised row that is absent, and bad pair counts
- Each is rejected with its own reason
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: verdicts equals `["reject:point-limit:0", "reject:point-limit:0",`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-FAILCLOSED
step("Decode sections with an unreadable point count, 4097 points, a promised row that is absent, and bad pair counts")
val verdicts = [
    outcome(join_point_section_decode_v2(sealed(joined([head("0"), ["x"]])))),
    outcome(join_point_section_decode_v2(sealed(joined([head("0"), ["4097"]])))),
    outcome(join_point_section_decode_v2(sealed(joined([head("0"), ["1"]])))),
    outcome(join_point_section_decode_v2(sealed(joined([head("0"), ["1", "x"], valid_pairs("f")])))),
    outcome(join_point_section_decode_v2(sealed(joined([head("0"), ["1", "6"], valid_pairs("f")])))),
    outcome(join_point_section_decode_v2(sealed(joined([head("0"), ["1", "5"], valid_pairs("f"), ["extra"]]))))]
step("Each is rejected with its own reason")
expect(verdicts).to_equal(["reject:point-limit:0", "reject:point-limit:0",
    "reject:truncated-section:0", "reject:truncated-row:0", "reject:truncated-row:0",
    "reject:trailing-data:0"])
```

</details>

#### an unknown optional field is ignored

- Add a `?`-prefixed field this reader does not know to a valid row
- The row decodes with its known fields unchanged
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: outcome(result) equals `ok::1`
   - Expected: result.section.points[0].attrs equals `["logged"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-CODEC
step("Add a `?`-prefixed field this reader does not know to a valid row")
var pairs = valid_pairs("submit_view")
pairs.push("?mir_site")
pairs.push("anything")
val result = one_point(pairs)
step("The row decodes with its known fields unchanged")
expect(outcome(result)).to_equal("ok::1")
expect([result.section.points[0].id, result.section.points[0].signature_digest]).to_equal(
    ["pay_a::submit_view", sha256_text("signature")])
expect(result.section.points[0].attrs).to_equal(["logged"])
```

</details>

#### a row with an unknown, repeated, missing or unreadable field is rejected

- Decode rows with a field lacking the `?` prefix, a repeated field, a dropped field and a broken attribute list
- Each is rejected with its own reason
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: verdicts equals `["reject:unknown-mandatory-field:0", "reject:duplicate-field:0",`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-FAILCLOSED
step("Decode rows with a field lacking the `?` prefix, a repeated field, a dropped field and a broken attribute list")
var unknown = valid_pairs("f")
unknown.push("around_site")
unknown.push("1")
var duplicate = valid_pairs("f")
duplicate.push("symbol")
duplicate.push("g")
val verdicts = [outcome(one_point(unknown)), outcome(one_point(duplicate)),
    outcome(one_point(without_key(valid_pairs("f"), "body"))),
    outcome(one_point(with_value(valid_pairs("f"), "attrs", "9:logged")))]
step("Each is rejected with its own reason")
expect(verdicts).to_equal(["reject:unknown-mandatory-field:0", "reject:duplicate-field:0",
    "reject:missing-field:0", "reject:bad-attrs:0"])
```

</details>

#### a decoded row must satisfy the builder's rules

- Decode a well-framed row with an empty signature digest, and a section whose two rows share a symbol
- Both are rejected with the builder's own reason
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: outcome(empty_signature) equals `reject:join-point-signature-unavailable:0`
   - Expected: outcome(twins) equals `reject:join-point-duplicate:0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-FAILCLOSED
step("Decode a well-framed row with an empty signature digest, and a section whose two rows share a symbol")
val empty_signature = one_point(with_value(valid_pairs("f"), "signature", ""))
val twins = join_point_section_decode_v2(sealed(joined([head("0"), ["2", "5"], valid_pairs("f"),
    ["5"], valid_pairs("f")])))
step("Both are rejected with the builder's own reason")
expect(outcome(empty_signature)).to_equal("reject:join-point-signature-unavailable:0")
expect(outcome(twins)).to_equal("reject:join-point-duplicate:0")
```

</details>

### join-point TLDR entry

#### a module TLDR carries exactly one section

- Render the entry among other TLDR sections, parse the TLDR text back, and read the section
- The TLDR parser admits the `join-point` kind and the section decodes with both rows
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: entry.starts_with("join-point|") is true
   - Expected: consumed equals `wire.byte_len()`
   - Expected: outcome(found) equals `ok::2`
   - Expected: ids(found.section.points) equals `["pay_a::audit_view", "pay_a::submit_view"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-CODEC
step("Render the entry among other TLDR sections, parse the TLDR text back, and read the section")
val entry = join_point_section_entry_v2(section_a()).unwrap()
val wire = module_tldr_sections_render_v1(["const|val LIMIT: i64 = 42", entry])
val (entries, consumed) = module_tldr_sections_parse_v1(wire)
val found = join_point_section_of_entries_v2(entries)
step("The TLDR parser admits the `join-point` kind and the section decodes with both rows")
expect(entry.starts_with("join-point|")).to_equal(true)
expect(consumed).to_equal(wire.byte_len())
expect(outcome(found)).to_equal("ok::2")
expect(ids(found.section.points)).to_equal(["pay_a::audit_view", "pay_a::submit_view"])
```

</details>

#### a TLDR without the section is a miss and a TLDR with two is rejected

- Read the section from entries that have none, from entries that have it twice, and encode an over-limit section
- Absence is a miss, duplication is a reject, and an over-limit section has no entry at all
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: outcome(join_point_section_of_entries_v2(["const|val LIMIT: i64 = 42"])) equals `miss:section-absent:0`
   - Expected: outcome(join_point_section_of_entries_v2([entry, entry])) equals `reject:duplicate-section:0`
   - Expected: join_point_section_entry_v2(JoinPointSectionV2(..section_a(), guards: many)).unwrap_err() equals `guard-limit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-FAILCLOSED
step("Read the section from entries that have none, from entries that have it twice, and encode an over-limit section")
val entry = join_point_section_entry_v2(section_a()).unwrap()
var many: [GuardEvalV1] = []
for i in 0..1025:
    many.push(guards_of_a()[0])
step("Absence is a miss, duplication is a reject, and an over-limit section has no entry at all")
expect(outcome(join_point_section_of_entries_v2(["const|val LIMIT: i64 = 42"]))).to_equal("miss:section-absent:0")
expect(outcome(join_point_section_of_entries_v2([entry, entry]))).to_equal("reject:duplicate-section:0")
expect(join_point_section_entry_v2(JoinPointSectionV2(..section_a(), guards: many)).unwrap_err()).to_equal("guard-limit")
```

</details>

### directory facts from sections

#### every member's section gives complete facts equal to the direct construction

- Build the facts of directory `pay` from the sections of its two members, in both section orders
- The facts are complete, independent of section order, and every join point has a body digest
   - Exec capture: after_step
   - Evidence: execution result verified by 5 expected checks
   - Expected: facts.complete is true
   - Expected: facts_summary(facts) equals `facts_summary(direct)`
   - Expected: facts_summary(swapped) equals `facts_summary(facts)`
   - Expected: facts.sorted_join_points.len() equals `direct_points.len()`
   - Expected: point.base_body_digest == "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-DIRECTORY
step("Build the facts of directory `pay` from the sections of its two members, in both section orders")
val files = ["pay/pay_a.spl", "pay/pay_b.spl"]
val facts = directory_join_point_facts_of_sections_v2("pay", files, [section_a(), section_b()], PROFILE)
val swapped = directory_join_point_facts_of_sections_v2("pay", files, [section_b(), section_a()], PROFILE)
var direct_points: [JoinPointFactV1] = []
for point in section_a().points:
    direct_points.push(join_point_fact_v1_of_v2(point))
for point in section_b().points:
    direct_points.push(join_point_fact_v1_of_v2(point))
val direct = directory_join_point_facts_guarded_v1("pay", files, direct_points, [], true,
    active_guard_root_v1(PROFILE, guards_of_a()))
step("The facts are complete, independent of section order, and every join point has a body digest")
expect(facts.complete).to_equal(true)
expect(facts_summary(facts)).to_equal(facts_summary(direct))
expect(facts_summary(swapped)).to_equal(facts_summary(facts))
expect(facts.sorted_join_points.len()).to_equal(direct_points.len())
for point in facts.sorted_join_points:
    expect(point.base_body_digest == "").to_equal(false)
```

</details>

#### a member without a section makes the facts incomplete

- Build the facts of a two-member directory from the section of one member only
- The facts are incomplete, so no shard computed from them can be admitted
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: facts.complete is false
   - Expected: facts.sorted_join_points.len() equals `section_a().points.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-DIRECTORY
step("Build the facts of a two-member directory from the section of one member only")
val facts = directory_join_point_facts_of_sections_v2("pay", ["pay/pay_a.spl", "pay/pay_b.spl"],
    [section_a()], PROFILE)
step("The facts are incomplete, so no shard computed from them can be admitted")
expect(facts.complete).to_equal(false)
expect(facts.sorted_join_points.len()).to_equal(section_a().points.len())
```

</details>

#### a foreign, repeated or other-profile section is left out and makes the facts incomplete

- Add a section of a file outside the directory, a second section of a member, and a section of another guard profile
- Each case is incomplete and the offending section's rows are not in the facts
   - Exec capture: after_step
   - Evidence: execution result verified by 4 expected checks
   - Expected: [with_outsider.complete, with_repeat.complete, with_profile.complete] equals `[false, false, false]`
   - Expected: with_outsider.sorted_join_points.len() equals `all_rows`
   - Expected: with_repeat.sorted_join_points.len() equals `all_rows`
   - Expected: with_profile.sorted_join_points.len() equals `section_a().points.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-DIRECTORY
step("Add a section of a file outside the directory, a second section of a member, and a section of another guard profile")
val files = ["pay/pay_a.spl", "pay/pay_b.spl"]
val outsider = join_point_section_v2("other", "other/x.spl", PROFILE, [], [row("x_view", [])]).unwrap()
val other_profile = JoinPointSectionV2(..section_b(), guard_profile: "windows/x86_64")
val with_outsider = directory_join_point_facts_of_sections_v2("pay", files,
    [section_a(), section_b(), outsider], PROFILE)
val with_repeat = directory_join_point_facts_of_sections_v2("pay", files,
    [section_a(), section_b(), section_a()], PROFILE)
val with_profile = directory_join_point_facts_of_sections_v2("pay", files,
    [section_a(), other_profile], PROFILE)
step("Each case is incomplete and the offending section's rows are not in the facts")
expect([with_outsider.complete, with_repeat.complete, with_profile.complete]).to_equal([false, false, false])
val all_rows = section_a().points.len() + section_b().points.len()
expect(with_outsider.sorted_join_points.len()).to_equal(all_rows)
expect(with_repeat.sorted_join_points.len()).to_equal(all_rows)
expect(with_profile.sorted_join_points.len()).to_equal(section_a().points.len())
```

</details>

### aspect_root_digest_v1

#### the root does not depend on the order of leaves or children

- Compute the root of two leaves and two child roots in every order
- All orders give one tagged sha256 root
   - Exec capture: after_step
   - Evidence: execution result verified by 3 expected checks
   - Expected: root.starts_with("sha256:") is true
   - Expected: aspect_root_digest_v1(["leaf-b", "leaf-a"], ["child-1", "child-2"]) equals `root`
   - Expected: aspect_root_digest_v1(["leaf-a", "leaf-b"], ["child-2", "child-1"]) equals `root`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-ROOT
step("Compute the root of two leaves and two child roots in every order")
val root = aspect_root_digest_v1(["leaf-a", "leaf-b"], ["child-1", "child-2"])
step("All orders give one tagged sha256 root")
expect(root.starts_with("sha256:")).to_equal(true)
expect(aspect_root_digest_v1(["leaf-b", "leaf-a"], ["child-1", "child-2"])).to_equal(root)
expect(aspect_root_digest_v1(["leaf-a", "leaf-b"], ["child-2", "child-1"])).to_equal(root)
```

</details>

#### the root changes with any leaf, any child, and their roles

- Change one leaf, one child, repeat a leaf, and move a digest from the leaves to the children
- Every variant is a different root, including the empty directory
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: variant == root is false
   - Expected: variants[4].starts_with("sha256:") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-ASPECT-AW2-ROOT
step("Change one leaf, one child, repeat a leaf, and move a digest from the leaves to the children")
val root = aspect_root_digest_v1(["leaf-a", "leaf-b"], ["child-1"])
val variants = [aspect_root_digest_v1(["leaf-a", "leaf-c"], ["child-1"]),
    aspect_root_digest_v1(["leaf-a", "leaf-b"], ["child-9"]),
    aspect_root_digest_v1(["leaf-a", "leaf-b", "leaf-b"], ["child-1"]),
    aspect_root_digest_v1(["leaf-a"], ["leaf-b", "child-1"]),
    aspect_root_digest_v1([], [])]
step("Every variant is a different root, including the empty directory")
for variant in variants:
    expect(variant == root).to_equal(false)
expect(variants[4].starts_with("sha256:")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-ASPECT-AW2-FACT`
- `REQ-ASPECT-AW2-CODEC`
- `REQ-ASPECT-AW2-FAILCLOSED`
- `REQ-ASPECT-AW2-DIRECTORY`
- `REQ-ASPECT-AW2-ROOT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9b28ac1459b9b9392874d17bcfad96506a2ee59d8bac4b8eed97e24b8072f98e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9b28ac1459b9b9392874d17bcfad96506a2ee59d8bac4b8eed97e24b8072f98e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9b28ac1459b9b9392874d17bcfad96506a2ee59d8bac4b8eed97e24b8072f98e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: 01_unit/compiler/aop/join_point_section_v2_spec.spl
mirror: doc/06_spec/01_unit/compiler/aop/join_point_section_v2_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/aop/join_point_section_v2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/aop/join_point_section_v2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
