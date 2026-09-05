# scv_file_identity_spec

> Purpose: This spec proves SCV's persistent FileEntityId foundation (report

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_file_identity_spec

Purpose: This spec proves SCV's persistent FileEntityId foundation (report

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_file_identity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV's persistent FileEntityId foundation (report
§7.6/§7.8/§7.9, P1 items 1+3): repo-unique `file_<n>` ids persisted in
`.scv/meta/file_identity.sdn`, immutable relation edges in
`.scv/meta/identity_edges.sdn`, and the evidence-based file matcher that
feeds them — exact rename keeps the id (accepted), rename+edit only
suggests, a copy allocates a new id, delete is terminal, ambiguity never
auto-accepts.
Audience: Maintainers of the SCV identity layer.

## Scenarios

### scv persistent file identity store

#### allocates, persists, and reloads a repo-unique file id

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allocates, persists, and reloads a repo-unique file id
- Allocate an id and read it back from the persisted store
   - Expected: id equals `file_1`
   - Expected: scv_identity_lookup_by_path(root, "a.txt") equals `id`
   - Expected: scv_identity_allocate(root, "a.txt", "c2") equals `id`
   - Expected: file_exists(scv_identity_rows_path(root)) is true
   - Expected: second equals `file_2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("allocates, persists, and reloads a repo-unique file id")
step("Allocate an id and read it back from the persisted store")
val root = _repo("alloc")
val id = scv_identity_allocate(root, "a.txt", "c1")
expect(id).to_equal("file_1")
expect(scv_identity_lookup_by_path(root, "a.txt")).to_equal(id)
# idempotent: re-allocating the same live path returns the same id
expect(scv_identity_allocate(root, "a.txt", "c2")).to_equal(id)
expect(file_exists(scv_identity_rows_path(root))).to_equal(true)
expect(file_read(scv_identity_rows_path(root))).to_contain("file_1|a.txt|c1|new|live")
val second = scv_identity_allocate(root, "b.txt", "c1")
expect(second).to_equal("file_2")
```

</details>

#### keeps the id across an exact-content rename via an accepted edge

- keeps the id across an exact-content rename via an accepted edge
- Classify prev->new trees where content moved byte-identically
- The same id now lives at the new path, with an accepted edge
   - Expected: scv_identity_lookup_by_path(root, "b.txt") equals `id`
   - Expected: scv_identity_lookup_by_path(root, "a.txt") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps the id across an exact-content rename via an accepted edge")
step("Classify prev->new trees where content moved byte-identically")
val root = _repo("move")
val id = scv_identity_allocate(root, "a.txt", "c1")
_chunk(root, "ck1", "line1\nline2\n")
val rows = scv_entity_apply(root, "a.txt|f1|ck1|10|0", "b.txt|f1|ck1|10|0", "c2")
expect(_joined(rows)).to_contain("move|a.txt|b.txt|1000")
step("The same id now lives at the new path, with an accepted edge")
expect(scv_identity_lookup_by_path(root, "b.txt")).to_equal(id)
expect(scv_identity_lookup_by_path(root, "a.txt")).to_equal("")
expect(file_read(scv_identity_edges_path(root))).to_contain("|move|c2|1000|exact_content,unique_pair|fim-1|accepted")
```

</details>

#### records rename+edit as a suggested edge without moving the id

- records rename+edit as a suggested edge without moving the id
- Classify a deleted and an added file sharing most lines
- The suggested edge carries the score and the id did NOT move
   - Expected: scv_identity_current_path(root, id) equals `a.txt`
   - Expected: new_id == "" or new_id == id is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("records rename+edit as a suggested edge without moving the id")
step("Classify a deleted and an added file sharing most lines")
val root = _repo("moveedit")
val id = scv_identity_allocate(root, "a.txt", "c1")
_chunk(root, "ck1", "l1\nl2\nl3\nl4\nl5\nl6\nl7\nl8\nl9\nl10\n")
_chunk(root, "ck2", "l1\nl2\nl3\nl4\nl5\nl6\nl7\nl8\nl9\nCHANGED\n")
val rows = scv_entity_apply(root, "a.txt|f1|ck1|40|0", "b.txt|f2|ck2|40|0", "c2")
expect(_joined(rows)).to_contain("move_edit|a.txt|b.txt|900")
step("The suggested edge carries the score and the id did NOT move")
expect(scv_identity_current_path(root, id)).to_equal("a.txt")
val new_id = scv_identity_lookup_by_path(root, "b.txt")
expect(new_id == "" or new_id == id).to_equal(false)
expect(file_read(scv_identity_edges_path(root))).to_contain("|move_edit|c2|900|line_overlap|fim-1|suggested")
```

</details>

#### allocates a new id plus copied_from edge for a copy

- allocates a new id plus copied_from edge for a copy
- Record a copy and verify a fresh id linked to the source
   - Expected: cp == src is false
   - Expected: scv_identity_lookup_by_path(root, "a.txt") equals `src`
   - Expected: scv_identity_lookup_by_path(root, "a_copy.txt") equals `cp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("allocates a new id plus copied_from edge for a copy")
step("Record a copy and verify a fresh id linked to the source")
val root = _repo("copy")
val src = scv_identity_allocate(root, "a.txt", "c1")
val cp = scv_identity_record_copy(root, "a.txt", "a_copy.txt", "c2", "user_copy")
expect(cp == src).to_equal(false)
expect(cp).to_contain("file_")
expect(scv_identity_lookup_by_path(root, "a.txt")).to_equal(src)
expect(scv_identity_lookup_by_path(root, "a_copy.txt")).to_equal(cp)
expect(file_read(scv_identity_rows_path(root))).to_contain("|copied_from:{src}|live")
expect(file_read(scv_identity_edges_path(root))).to_contain("{src}|{cp}|copy|c2|1000|user_copy|fim-1|accepted")
```

</details>

#### treats delete as terminal and never reuses the id

- treats delete as terminal and never reuses the id
- Delete a file, then allocate a new one
   - Expected: scv_identity_record_delete(root, "a.txt", "c2") equals `id`
   - Expected: scv_identity_state(root, id) equals `deleted`
   - Expected: scv_identity_lookup_by_path(root, "a.txt") equals ``
- A later file at the same path gets a FRESH id
   - Expected: re == id is false
   - Expected: scv_identity_state(root, id) equals `deleted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("treats delete as terminal and never reuses the id")
step("Delete a file, then allocate a new one")
val root = _repo("delete")
val id = scv_identity_allocate(root, "a.txt", "c1")
expect(scv_identity_record_delete(root, "a.txt", "c2")).to_equal(id)
expect(scv_identity_state(root, id)).to_equal("deleted")
expect(scv_identity_lookup_by_path(root, "a.txt")).to_equal("")
step("A later file at the same path gets a FRESH id")
val re = scv_identity_allocate(root, "a.txt", "c3")
expect(re == id).to_equal(false)
expect(scv_identity_state(root, id)).to_equal("deleted")
```

</details>

#### keeps ambiguous identical-content matches suggested, never accepted

- keeps ambiguous identical-content matches suggested, never accepted
- One deleted file matches two identical added files
- The id stays at its old path; edge is suggested only
   - Expected: scv_identity_current_path(root, id) equals `a.txt`
   - Expected: file_read(scv_identity_edges_path(root)) contains `exact_content,ambiguous`
   - Expected: scv_identity_lookup_by_path(root, "x.txt") == "" is false
   - Expected: scv_identity_lookup_by_path(root, "y.txt") == "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps ambiguous identical-content matches suggested, never accepted")
step("One deleted file matches two identical added files")
val root = _repo("ambig")
val id = scv_identity_allocate(root, "a.txt", "c1")
_chunk(root, "ck1", "same\ncontent\n")
val rows = scv_entity_apply(root, "a.txt|f1|ck1|12|0", "x.txt|f2|ck1|12|0\ny.txt|f3|ck1|12|0", "c2")
expect(_joined(rows)).to_contain("move_ambiguous|a.txt|")
step("The id stays at its old path; edge is suggested only")
expect(scv_identity_current_path(root, id)).to_equal("a.txt")
expect(file_read(scv_identity_edges_path(root))).to_contain("|suggested")
expect(file_read(scv_identity_edges_path(root)).contains("exact_content,ambiguous")).to_equal(true)
# both added files got their own fresh ids
expect(scv_identity_lookup_by_path(root, "x.txt") == "").to_equal(false)
expect(scv_identity_lookup_by_path(root, "y.txt") == "").to_equal(false)
```

</details>

#### returns ordered relation history for an id

- returns ordered relation history for an id
- create -> accepted move -> delete, in order
   - Expected: hist.len() equals `3`
   - Expected: hist[0] equals `c1|create|accepted|1000`
   - Expected: hist[1] equals `c2|move|accepted|1000`
   - Expected: hist[2] equals `c3|delete|accepted|1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("returns ordered relation history for an id")
step("create -> accepted move -> delete, in order")
val root = _repo("history")
val id = scv_identity_allocate(root, "a.txt", "c1")
scv_identity_record_move(root, "a.txt", "b.txt", "c2", "exact_content", 1000, "accepted")
scv_identity_record_delete(root, "b.txt", "c3")
val hist = scv_identity_history(root, id)
expect(hist.len()).to_equal(3)
expect(hist[0]).to_equal("c1|create|accepted|1000")
expect(hist[1]).to_equal("c2|move|accepted|1000")
expect(hist[2]).to_equal("c3|delete|accepted|1000")
```

</details>

#### classifies unchanged, edited, new and deleted correctly

- classifies unchanged, edited, new and deleted correctly
- Mixed tree delta
- Line overlap scorer sanity
   - Expected: scv_entity_line_overlap_milli("a\nb\n", "a\nb\n") equals `1000`
   - Expected: scv_entity_line_overlap_milli("a\nb\n", "x\ny\n") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("classifies unchanged, edited, new and deleted correctly")
step("Mixed tree delta")
val root = _repo("classify")
_chunk(root, "ck1", "a\n")
_chunk(root, "ck2", "b\n")
_chunk(root, "ck3", "totally\ndifferent\n")
val prev = "same.txt|f1|ck1|2|0\nedit.txt|f2|ck2|2|0\ngone.txt|f3|ck3|10|0"
val new_tree = "same.txt|f1|ck1|2|0\nedit.txt|f4|ck1|2|0\nfresh.txt|f5|ck2|2|0"
val rows = _joined(scv_entity_classify(root, prev, new_tree))
expect(rows).to_contain("unchanged|same.txt")
expect(rows).to_contain("edited|edit.txt")
expect(rows).to_contain("deleted|gone.txt")
expect(rows).to_contain("new|fresh.txt")
step("Line overlap scorer sanity")
expect(scv_entity_line_overlap_milli("a\nb\n", "a\nb\n")).to_equal(1000)
expect(scv_entity_line_overlap_milli("a\nb\n", "x\ny\n")).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-FILE-IDENTITY-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `182b7c65ad495e69c387a1943f90c505f4c75d5c632fe044c4d50b00b99235ee`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `182b7c65ad495e69c387a1943f90c505f4c75d5c632fe044c4d50b00b99235ee`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `182b7c65ad495e69c387a1943f90c505f4c75d5c632fe044c4d50b00b99235ee`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_file_identity_spec.spl
mirror: doc/06_spec/integration/app/scv_file_identity_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/integration/app/scv_file_identity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_file_identity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_file_identity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/scv_file_identity_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_file_identity_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates, persists, and reloads a repo-unique file id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_file_identity_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the id across an exact-content rename via an accepted edge' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_file_identity_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records rename+edit as a suggested edge without moving the id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
