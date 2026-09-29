# scv_edit_graph_spec

> Purpose: This spec proves SCV-IMPL-D-03 — the refactoring-aware edit graph:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_edit_graph_spec

Purpose: This spec proves SCV-IMPL-D-03 — the refactoring-aware edit graph:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_edit_graph_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV-IMPL-D-03 — the refactoring-aware edit graph:
one diff report that links raw hunks <-> symbol entities <-> inferred
refactoring operations (I-04 rows), built from the SAME status-index vs
working-copy comparison the D-02 views render, and exposed as
`scv diff --view graph`.
Audience: Maintainers of the SCV diff layer.

## Scenarios

### scv refactoring-aware edit graph (D-03)

#### splits a change into anchored hunks with old/new ranges

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- common suffix trimmed, unique line anchors the middle
   - Expected: hunks.len() equals `2`
   - Expected: hunks[0].old_start equals `1`
   - Expected: hunks[0].old_len equals `1`
   - Expected: hunks[0].new_start equals `1`
   - Expected: hunks[0].new_len equals `1`
   - Expected: hunks[1].old_len equals `0`
   - Expected: hunks[1].new_start equals `3`
   - Expected: hunks[1].new_len equals `1`
- identical texts yield no hunk; bounds are named constants
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: scv_eg_hunks("a.spl", "same\n", "same\n").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-EDIT-GRAPH-001
step("common suffix trimmed, unique line anchors the middle")
val hunks = scv_eg_hunks("a.spl", "fn alpha():\n    x = 1\n", "fn beta():\n    x = 1\n    y = 2\n")
expect(hunks.len()).to_equal(2)
expect(hunks[0].old_start).to_equal(1)
expect(hunks[0].old_len).to_equal(1)
expect(hunks[0].new_start).to_equal(1)
expect(hunks[0].new_len).to_equal(1)
expect(hunks[1].old_len).to_equal(0)
expect(hunks[1].new_start).to_equal(3)
expect(hunks[1].new_len).to_equal(1)
step("identical texts yield no hunk; bounds are named constants")
expect(scv_eg_hunks("a.spl", "same\n", "same\n").len()).to_equal(0)
expect(SCV_EDIT_GRAPH_MAX_ANCHORS > 0).to_be(true)
expect(SCV_EDIT_GRAPH_MAX_LINES > 0).to_be(true)
```

</details>

#### links hunks to entities and entities to the inferred refactoring op

- Build the graph from one modified file and read its hunk/entity/op links


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-EDIT-GRAPH-001
step("Build the graph from one modified file and read its hunk/entity/op links")
val out = scv_edit_graph_from_files([EditGraphFile(old_rel: "a.spl", new_rel: "a.spl", old_text: "fn alpha():\n    x = 1\n", new_text: "fn beta():\n    x = 1\n    y = 2\n")])
expect(out).to_contain("edit-graph files=1 hunks=2 entities=2 ops=1\n")
expect(out).to_contain("file a.spl modified\n")
expect(out).to_contain("hunk h1 a.spl -1,1 +1,1\n")
expect(out).to_contain("hunk h2 a.spl -2,0 +3,1\n")
expect(out).to_contain("entity e1 a.spl:fn:alpha old=1-2 new=-\n")
expect(out).to_contain("entity e2 a.spl:fn:beta old=- new=1-3\n")
expect(out).to_contain("op r1 rename a.spl:fn:alpha -> a.spl:fn:beta ")
expect(out).to_contain("link hunk h1 -> entity e1\n")
expect(out).to_contain("link hunk h1 -> entity e2\n")
expect(out).to_contain("link hunk h2 -> entity e2\n")
expect(out).to_contain("link entity e1 -> op r1\n")
expect(out).to_contain("link entity e2 -> op r1\n")
```

</details>

#### carries a cross-file move as a many-to-many op over both files

- Move a symbol across files and read the many-to-many move op


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-EDIT-GRAPH-001
step("Move a symbol across files and read the many-to-many move op")
var files: [EditGraphFile] = []
files.push(EditGraphFile(old_rel: "a.spl", new_rel: "a.spl", old_text: "fn alpha():\n    x = 1\n    y = 2\nfn keep():\n    pass\n", new_text: "fn keep():\n    pass\n"))
files.push(EditGraphFile(old_rel: "", new_rel: "b.spl", old_text: "", new_text: "fn alpha():\n    x = 1\n    y = 2\n"))
val out = scv_edit_graph_from_files(files)
expect(out).to_contain("file b.spl added\n")
expect(out).to_contain("op r1 move a.spl:fn:alpha -> b.spl:fn:alpha 1000 accepted\n")
expect(out).to_contain("link entity e1 -> op r1\n")
expect(out).to_contain("link entity e3 -> op r1\n")
```

</details>

#### is exposed as `diff --view graph` over the repository comparison

- no working-copy change -> no changes
   - Protocol capture: after_step
   - Evidence: protocol response verified by 1 expected check
   - Expected: scv_edit_graph(root) equals `no changes\n`
- rename the fn -> graph view with the rename op


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-EDIT-GRAPH-001
val root = _repo("view")
file_write("{root}/a.spl", "fn alpha():\n    x = 1\n")
scv_snapshot_with_identity(root, _no_hints())
step("no working-copy change -> no changes")
expect(scv_edit_graph(root)).to_equal("no changes\n")
step("rename the fn -> graph view with the rename op")
file_write("{root}/a.spl", "fn beta():\n    x = 1\n    y = 2\n")
val out = scv_diff_views(root, "graph", false)
expect(out.starts_with("view=graph\nedit-graph files=1 ")).to_be(true)
expect(out).to_contain("op r1 rename a.spl:fn:alpha -> a.spl:fn:beta ")
expect(out).to_contain("link hunk h1 -> entity e1\n")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SCV-EDIT-GRAPH-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d3938cafa3b4513f2db0f514677c0c8b8e4f944ce326657039f7f6d3c59fddda`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d3938cafa3b4513f2db0f514677c0c8b8e4f944ce326657039f7f6d3c59fddda`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d3938cafa3b4513f2db0f514677c0c8b8e4f944ce326657039f7f6d3c59fddda`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/integration/app/scv_edit_graph_spec.spl
mirror: doc/06_spec/integration/app/scv_edit_graph_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_edit_graph_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_edit_graph_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_edit_graph_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/scv_edit_graph_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'carries a cross-file move as a many-to-many op over both files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
