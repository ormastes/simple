# scv_file_history_spec

> Purpose: This spec proves SCV-IMPL-I-02 — FileEntityId is resolved on every

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_file_history_spec

Purpose: This spec proves SCV-IMPL-I-02 — FileEntityId is resolved on every

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_file_history_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV-IMPL-I-02 — FileEntityId is resolved on every
implicit snapshot (`scv_snapshot_with_identity`) and surfaced by the
`scv file-history` CLI path. Covered evidence order: editor-txn rename hint >
rename pair (incl. case-only rename) > exact content > similarity >
user-pending. Atomic save (tmp-write-rename-delete) coalesces to a plain
content update of the target path and keeps its id.
Audience: Maintainers of the SCV identity layer.

## Scenarios

### scv file-history snapshot integration (I-02)

#### allocates an id on the first snapshot and reports its history

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- allocates an id on the first snapshot and reports its history
- Snapshot one file and read its file-history


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("allocates an id on the first snapshot and reports its history")
step("Snapshot one file and read its file-history")
val root = _repo("alloc")
file_write("{root}/a.txt", "alpha\nbeta\n")
val out = scv_snapshot_with_identity(root, _no_hints())
expect(out.starts_with("snapshot ")).to_be(true)
expect(out).to_contain("create a.txt")
val id = scv_identity_lookup_by_path(root, "a.txt")
expect(id.starts_with("file_")).to_be(true)
val history = scv_file_history(root, "a.txt")
expect(history).to_contain("file-history {id}")
expect(history).to_contain("path: a.txt")
expect(history).to_contain("state: live")
expect(history).to_contain("|create|accepted|")
```

</details>

#### keeps the id across an exact-content rename (accepted move)

- keeps the id across an exact-content rename (accepted move)
- Rename a file without editing it between snapshots


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps the id across an exact-content rename (accepted move)")
step("Rename a file without editing it between snapshots")
val root = _repo("rename")
file_write("{root}/a.txt", "same content\nline two\n")
scv_snapshot_with_identity(root, _no_hints())
val id = scv_identity_lookup_by_path(root, "a.txt")
file_delete("{root}/a.txt")
file_write("{root}/b.txt", "same content\nline two\n")
val out = scv_snapshot_with_identity(root, _no_hints())
expect(out).to_contain("move a.txt -> b.txt evidence=exact_content status=accepted")
expect(scv_identity_lookup_by_path(root, "b.txt")).to_be(id)
expect(scv_identity_current_path(root, id)).to_be("b.txt")
val history = scv_file_history(root, id)
expect(history).to_contain("|move|accepted|")
```

</details>

#### only suggests on rename+edit and never moves current_path

- only suggests on rename+edit and never moves current_path
- Rename with a substantial edit; similarity suggests, does not accept


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("only suggests on rename+edit and never moves current_path")
step("Rename with a substantial edit; similarity suggests, does not accept")
val root = _repo("renameedit")
file_write("{root}/a.txt", "one\ntwo\nthree\nfour\nfive\n")
scv_snapshot_with_identity(root, _no_hints())
val id = scv_identity_lookup_by_path(root, "a.txt")
file_delete("{root}/a.txt")
file_write("{root}/moved.txt", "one\ntwo\nthree\nfour\nCHANGED\n")
val out = scv_snapshot_with_identity(root, _no_hints())
expect(out).to_contain("evidence=similarity status=suggested")
expect(scv_identity_current_path(root, id)).to_be("a.txt")
# the new path gets a pending id of its own until the user accepts
val new_id = scv_identity_lookup_by_path(root, "moved.txt")
expect(new_id.starts_with("file_")).to_be(true)
expect(new_id == id).to_be(false)
```

</details>

#### accepts a case-only rename as a rename pair

- accepts a case-only rename as a rename pair
- Rename a.txt -> A.txt with an edit; case pairing outranks similarity


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("accepts a case-only rename as a rename pair")
step("Rename a.txt -> A.txt with an edit; case pairing outranks similarity")
val root = _repo("caseonly")
file_write("{root}/notes.txt", "n1\nn2\n")
scv_snapshot_with_identity(root, _no_hints())
val id = scv_identity_lookup_by_path(root, "notes.txt")
file_delete("{root}/notes.txt")
file_write("{root}/NOTES.txt", "n1\nn2\nn3-added\n")
val out = scv_snapshot_with_identity(root, _no_hints())
expect(out).to_contain("evidence=case_rename status=accepted")
expect(scv_identity_current_path(root, id)).to_be("NOTES.txt")
```

</details>

#### accepts an editor-txn rename hint over weak similarity

- accepts an editor-txn rename hint over weak similarity
- Heavy edit + rename with an explicit hint is accepted as rename_pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("accepts an editor-txn rename hint over weak similarity")
step("Heavy edit + rename with an explicit hint is accepted as rename_pair")
val root = _repo("hint")
file_write("{root}/x.txt", "aa\nbb\ncc\n")
scv_snapshot_with_identity(root, _no_hints())
val id = scv_identity_lookup_by_path(root, "x.txt")
file_delete("{root}/x.txt")
file_write("{root}/y.txt", "totally\ndifferent\ncontent\n")
val out = scv_snapshot_with_identity(root, ["x.txt|y.txt"])
expect(out).to_contain("move x.txt -> y.txt evidence=rename_pair status=accepted")
expect(scv_identity_current_path(root, id)).to_be("y.txt")
```

</details>

#### treats an atomic save as a content update, and a real delete as terminal

- treats an atomic save as a content update, and a real delete as terminal
- tmp-write-rename-delete keeps the target id; delete flips state


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("treats an atomic save as a content update, and a real delete as terminal")
step("tmp-write-rename-delete keeps the target id; delete flips state")
val root = _repo("atomic")
file_write("{root}/doc.txt", "v1\n")
scv_snapshot_with_identity(root, _no_hints())
val id = scv_identity_lookup_by_path(root, "doc.txt")
# atomic save: tmp file existed only between snapshots — the snapshot
# sees just the target path with new content
file_write("{root}/doc.txt", "v2\n")
val out = scv_snapshot_with_identity(root, _no_hints())
expect(scv_identity_lookup_by_path(root, "doc.txt")).to_be(id)
expect(out.contains("delete doc.txt")).to_be(false)
file_delete("{root}/doc.txt")
val out2 = scv_snapshot_with_identity(root, _no_hints())
expect(out2).to_contain("delete doc.txt")
expect(scv_identity_state(root, id)).to_be("deleted")
```

</details>

#### reports an honest error for an unknown target

- reports an honest error for an unknown target
- file-history on a path with no identity is an ERROR


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports an honest error for an unknown target")
step("file-history on a path with no identity is an ERROR")
val root = _repo("unknown")
val out = scv_file_history(root, "nope.txt")
expect(out.starts_with("ERROR")).to_be(true)
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
- `REQ-SCV-FILE-HISTORY-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dcd8684e51cb412512ebdfc5d610c771ac714ea44bcd493a0723f802c8d52a26`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dcd8684e51cb412512ebdfc5d610c771ac714ea44bcd493a0723f802c8d52a26`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dcd8684e51cb412512ebdfc5d610c771ac714ea44bcd493a0723f802c8d52a26`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_file_history_spec.spl
mirror: doc/06_spec/integration/app/scv_file_history_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_file_history_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_file_history_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_file_history_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_file_history_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allocates an id on the first snapshot and reports its history' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_file_history_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the id across an exact-content rename (accepted move)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_file_history_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'only suggests on rename+edit and never moves current_path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
