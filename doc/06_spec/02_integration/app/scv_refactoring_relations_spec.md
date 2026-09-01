# scv_refactoring_relations_spec

> Purpose: This spec proves SCV-IMPL-I-04 — refactoring relations inferred

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_refactoring_relations_spec

Purpose: This spec proves SCV-IMPL-I-04 — refactoring relations inferred

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_refactoring_relations_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV-IMPL-I-04 — refactoring relations inferred
as many-to-many lineage edges over symbol declarations: rename / move /
move_rename / extract / inline / split / merge / pull_up / push_down /
signature_change.  The matcher is anchors -> bounded GumTree-style pairing
over indexed candidates -> RefactoringMiner-style rules; its bounds are
named constants and a tie between candidates is reported `ambiguous`, never
accepted.
Audience: Maintainers of the SCV identity layer and the D-03/D-04 lanes.

## Scenarios

### scv refactoring relations (I-04)

#### reports a same-file rename with an identical body as an accepted edge

**Manual warnings:**
- invalid manual visibility metadata: # @manual SCV commit gates (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-REFACTORING-RELATIONS-001
# @req REQ-SSPEC-INTEGRATION
val rows = scv_refactor_infer(_one("a.spl", "fn alpha():\n    x = 1\n    y = 2\n", "fn beta():\n    x = 1\n    y = 2\n"))
val renames = scv_refactor_rows_of_kind(rows, "rename")
expect(renames.len()).to_equal(1)
expect(_field(renames[0], 1)).to_equal("a.spl:fn:alpha")
expect(_field(renames[0], 2)).to_equal("a.spl:fn:beta")
expect(_field(renames[0], 5)).to_equal("accepted")
```

</details>

#### distinguishes move from move_rename across files

- same name in another file -> move
   - Expected: moves.len() equals `1`
   - Expected: _field(moves[0], 1) equals `a.spl:fn:alpha`
   - Expected: _field(moves[0], 2) equals `b.spl:fn:alpha`
- new name in another file -> move_rename
   - Expected: mr.len() equals `1`
   - Expected: _field(mr[0], 2) equals `b.spl:fn:gamma`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-REFACTORING-RELATIONS-001
step("same name in another file -> move")
var files = _one("a.spl", "fn alpha():\n    x = 1\n    y = 2\nfn keep():\n    pass\n", "fn keep():\n    pass\n")
files.push(RefactorFileInput(rel: "b.spl", old_text: "", new_text: "fn alpha():\n    x = 1\n    y = 2\n"))
val moves = scv_refactor_rows_of_kind(scv_refactor_infer(files), "move")
expect(moves.len()).to_equal(1)
expect(_field(moves[0], 1)).to_equal("a.spl:fn:alpha")
expect(_field(moves[0], 2)).to_equal("b.spl:fn:alpha")
step("new name in another file -> move_rename")
var files2 = _one("a.spl", "fn alpha():\n    x = 1\n    y = 2\n", "")
files2.push(RefactorFileInput(rel: "b.spl", old_text: "", new_text: "fn gamma():\n    x = 1\n    y = 2\n"))
val mr = scv_refactor_rows_of_kind(scv_refactor_infer(files2), "move_rename")
expect(mr.len()).to_equal(1)
expect(_field(mr[0], 2)).to_equal("b.spl:fn:gamma")
```

</details>

#### infers extract and inline from lines that reappear in another unit

- extract: removed lines of an anchored fn reappear in a new fn
   - Expected: ext.len() equals `1`
   - Expected: _field(ext[0], 1) equals `a.spl:fn:big`
   - Expected: _field(ext[0], 2) equals `a.spl:fn:big,a.spl:fn:helper`
- inline: a deleted fn's lines reappear inside the grown fn
   - Expected: inl.len() equals `1`
   - Expected: _field(inl[0], 1) equals `a.spl:fn:helper,a.spl:fn:big`
   - Expected: _field(inl[0], 2) equals `a.spl:fn:big`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-REFACTORING-RELATIONS-001
step("extract: removed lines of an anchored fn reappear in a new fn")
val ext = scv_refactor_rows_of_kind(scv_refactor_infer(_one("a.spl", "fn big():\n    a = 1\n    b = 2\n    c = 3\n    d = 4\n", "fn big():\n    a = 1\n    b = 2\n    helper()\nfn helper():\n    c = 3\n    d = 4\n")), "extract")
expect(ext.len()).to_equal(1)
expect(_field(ext[0], 1)).to_equal("a.spl:fn:big")
expect(_field(ext[0], 2)).to_equal("a.spl:fn:big,a.spl:fn:helper")
step("inline: a deleted fn's lines reappear inside the grown fn")
val inl = scv_refactor_rows_of_kind(scv_refactor_infer(_one("a.spl", "fn big():\n    a = 1\n    b = 2\n    helper()\nfn helper():\n    c = 3\n    d = 4\n", "fn big():\n    a = 1\n    b = 2\n    c = 3\n    d = 4\n")), "inline")
expect(inl.len()).to_equal(1)
expect(_field(inl[0], 1)).to_equal("a.spl:fn:helper,a.spl:fn:big")
expect(_field(inl[0], 2)).to_equal("a.spl:fn:big")
```

</details>

#### infers split and merge as many-to-many edges, not as renames

- split: one deleted fn -> two added fns holding its lines
   - Expected: split.len() equals `1`
   - Expected: _field(split[0], 1) equals `a.spl:fn:big`
   - Expected: _field(split[0], 2) equals `a.spl:fn:p1,a.spl:fn:p2`
   - Expected: scv_refactor_rows_of_kind(rows, "rename").len() equals `0`
- merge: two deleted fns -> one added fn holding both bodies
   - Expected: merge.len() equals `1`
   - Expected: _field(merge[0], 1) equals `a.spl:fn:p1,a.spl:fn:p2`
   - Expected: _field(merge[0], 2) equals `a.spl:fn:big`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-REFACTORING-RELATIONS-001
step("split: one deleted fn -> two added fns holding its lines")
val rows = scv_refactor_infer(_one("a.spl", "fn big():\n    a = 1\n    b = 2\n    c = 3\n    d = 4\n", "fn p1():\n    a = 1\n    b = 2\nfn p2():\n    c = 3\n    d = 4\n"))
val split = scv_refactor_rows_of_kind(rows, "split")
expect(split.len()).to_equal(1)
expect(_field(split[0], 1)).to_equal("a.spl:fn:big")
expect(_field(split[0], 2)).to_equal("a.spl:fn:p1,a.spl:fn:p2")
expect(scv_refactor_rows_of_kind(rows, "rename").len()).to_equal(0)
step("merge: two deleted fns -> one added fn holding both bodies")
val rows2 = scv_refactor_infer(_one("a.spl", "fn p1():\n    a = 1\n    b = 2\nfn p2():\n    c = 3\n    d = 4\n", "fn big():\n    a = 1\n    b = 2\n    c = 3\n    d = 4\n"))
val merge = scv_refactor_rows_of_kind(rows2, "merge")
expect(merge.len()).to_equal(1)
expect(_field(merge[0], 1)).to_equal("a.spl:fn:p1,a.spl:fn:p2")
expect(_field(merge[0], 2)).to_equal("a.spl:fn:big")
```

</details>

#### classifies member moves between a type and a trait as pull_up / push_down

- type -> trait is pull_up
   - Expected: up.len() equals `1`
   - Expected: _field(up[0], 1) equals `a.spl:fn:Foo.run`
   - Expected: _field(up[0], 2) equals `a.spl:fn:Bar.run`
- trait -> type is push_down
   - Expected: down.len() equals `1`
   - Expected: _field(down[0], 1) equals `a.spl:fn:Bar.run`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-REFACTORING-RELATIONS-001
val type_first = "class Foo:\n    me run():\n        a = 1\n        b = 2\ntrait Bar:\n    me idle():\n        pass\n"
val trait_first = "class Foo:\n    me other():\n        pass\ntrait Bar:\n    me run():\n        a = 1\n        b = 2\n"
step("type -> trait is pull_up")
val up = scv_refactor_rows_of_kind(scv_refactor_infer(_one("a.spl", type_first, trait_first)), "pull_up")
expect(up.len()).to_equal(1)
expect(_field(up[0], 1)).to_equal("a.spl:fn:Foo.run")
expect(_field(up[0], 2)).to_equal("a.spl:fn:Bar.run")
step("trait -> type is push_down")
val down = scv_refactor_rows_of_kind(scv_refactor_infer(_one("a.spl", trait_first, type_first)), "push_down")
expect(down.len()).to_equal(1)
expect(_field(down[0], 1)).to_equal("a.spl:fn:Bar.run")
```

</details>

#### reports a signature change on an anchored fn as accepted

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-REFACTORING-RELATIONS-001
val rows = scv_refactor_infer(_one("a.spl", "fn alpha(x: i64):\n    y = x\n", "fn alpha(x: i64, z: i64):\n    y = x\n"))
val sig = scv_refactor_rows_of_kind(rows, "signature_change")
expect(sig.len()).to_equal(1)
expect(_field(sig[0], 5)).to_equal("accepted")
expect(scv_refactor_rows_of_kind(rows, "rename").len()).to_equal(0)
```

</details>

#### never silently accepts an ambiguous match and records its bounds

- two identical candidates tie -> one ambiguous row listing both, no accepted edge
   - Expected: renames.len() equals `1`
   - Expected: _field(renames[0], 5) equals `ambiguous`
   - Expected: accepted equals `0`
- the matcher bound is a named, exported constant
   - Expected: SCV_REFACTOR_MAX_PAIRS equals `512`
- declaration units carry the body lines the matcher scores
   - Expected: units.len() equals `1`
   - Expected: units[0].body.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-REFACTORING-RELATIONS-001
step("two identical candidates tie -> one ambiguous row listing both, no accepted edge")
val rows = scv_refactor_infer(_one("a.spl", "fn alpha():\n    x = 1\n    y = 2\n", "fn beta():\n    x = 1\n    y = 2\nfn gamma():\n    x = 1\n    y = 2\n"))
val renames = scv_refactor_rows_of_kind(rows, "rename")
expect(renames.len()).to_equal(1)
expect(_field(renames[0], 5)).to_equal("ambiguous")
expect(_field(renames[0], 2).contains("a.spl:fn:beta")).to_be(true)
expect(_field(renames[0], 2).contains("a.spl:fn:gamma")).to_be(true)
var accepted = 0
for row in rows:
    if _field(row, 5) == "accepted":
        accepted = accepted + 1
expect(accepted).to_equal(0)
step("the matcher bound is a named, exported constant")
expect(SCV_REFACTOR_MAX_PAIRS).to_equal(512)
expect(SCV_REFACTOR_CANDIDATES_PER_UNIT > 0).to_be(true)
expect(SCV_REFACTOR_AMBIGUITY_MARGIN_MILLI > 0).to_be(true)
step("declaration units carry the body lines the matcher scores")
val units = scv_refactor_units("a.spl", "fn alpha():\n    x = 1\n\n    y = 2\n")
expect(units.len()).to_equal(1)
expect(units[0].body.len()).to_equal(2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-REFACTORING-RELATIONS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d1824c8e5a28fde385f5889c0b9a1fd8275ca1ab800af26412e7bd6af19e3337`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d1824c8e5a28fde385f5889c0b9a1fd8275ca1ab800af26412e7bd6af19e3337`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d1824c8e5a28fde385f5889c0b9a1fd8275ca1ab800af26412e7bd6af19e3337`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/02_integration/app/scv_refactoring_relations_spec.spl
mirror: doc/06_spec/02_integration/app/scv_refactoring_relations_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=80 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/scv_refactoring_relations_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/scv_refactoring_relations_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/scv_refactoring_relations_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 17 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/scv_refactoring_relations_spec.spl:33:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reports a same-file rename with an identical body as an accepted edge' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/02_integration/app/scv_refactoring_relations_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'distinguishes move from move_rename across files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/scv_refactoring_relations_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infers extract and inline from lines that reappear in another unit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/scv_refactoring_relations_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'infers split and merge as many-to-many edges, not as renames' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/scv_refactoring_relations_spec.spl:102:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'reports a signature change on an anchored fn as accepted' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
