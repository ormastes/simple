# scv_three_view_diff_spec

> Purpose: This spec proves SCV-IMPL-D-02 — one comparison rendered as

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_three_view_diff_spec

Purpose: This spec proves SCV-IMPL-D-02 — one comparison rendered as

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_three_view_diff_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV-IMPL-D-02 — one comparison rendered as
`--view raw|syntax|entity|semantic|all`, plus `--git-patch`: an
always-applicable Git patch export built from whole-file hunks. The entity
view relabels rows by persistent FileEntityId so a rename stays the same
entity; an invalid view name is an honest ERROR.
Audience: Maintainers of the SCV diff layer.

## Scenarios

### scv three-view diff (D-02)

#### rejects an unknown view name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects an unknown view name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("rejects an unknown view name")
val root = _repo("badview")
val out = scv_diff_views(root, "bogus", false)
expect(out.starts_with("ERROR")).to_be(true)
```

</details>

#### renders raw, syntax, entity, and semantic sections from one comparison

- renders raw, syntax, entity, and semantic sections from one comparison
- Snapshot, modify one file, render --view all


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders raw, syntax, entity, and semantic sections from one comparison")
step("Snapshot, modify one file, render --view all")
val root = _repo("all")
file_write("{root}/a.txt", "one\ntwo\n")
scv_snapshot_with_identity(root, _no_hints())
file_write("{root}/a.txt", "one\ntwo\nthree\n")
val out = scv_diff_views(root, "all", false)
expect(out).to_contain("view=raw")
expect(out).to_contain("view=syntax")
expect(out).to_contain("view=entity")
expect(out).to_contain("view=semantic")
expect(out).to_contain("modified a.txt")
val id = scv_identity_lookup_by_path(root, "a.txt")
expect(out).to_contain("entity {id} modified a.txt")
```

</details>

#### labels the syntax view with structural_source provenance

- labels the syntax view with structural_source provenance


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("labels the syntax view with structural_source provenance")
val root = _repo("syntax")
file_write("{root}/s.txt", "alpha\n")
scv_snapshot_with_identity(root, _no_hints())
file_write("{root}/s.txt", "alpha\nbeta\n")
val out = scv_diff_views(root, "syntax", false)
expect(out).to_contain("view=syntax")
expect(out).to_contain("structural_source=")
```

</details>

#### exports an always-applicable git patch with whole-file hunks

- exports an always-applicable git patch with whole-file hunks
- Modify + add + delete, then check the patch shape


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("exports an always-applicable git patch with whole-file hunks")
step("Modify + add + delete, then check the patch shape")
val root = _repo("patch")
file_write("{root}/keep.txt", "k1\nk2\n")
file_write("{root}/gone.txt", "g1\n")
scv_snapshot_with_identity(root, _no_hints())
file_write("{root}/keep.txt", "k1\nk2-edited\n")
file_write("{root}/new.txt", "n1\nn2\nn3\n")
file_delete("{root}/gone.txt")
val patch = scv_git_patch(root)
expect(patch).to_contain("diff --git a/keep.txt b/keep.txt")
expect(patch).to_contain("@@ -1,2 +1,2 @@")
expect(patch).to_contain("-k2\n")
expect(patch).to_contain("+k2-edited\n")
expect(patch).to_contain("diff --git a/new.txt b/new.txt")
expect(patch).to_contain("new file mode 100644")
expect(patch).to_contain("@@ -0,0 +1,3 @@")
expect(patch).to_contain("diff --git a/gone.txt b/gone.txt")
expect(patch).to_contain("deleted file mode 100644")
expect(patch).to_contain("@@ -1,1 +0,0 @@")
```

</details>

#### appends the patch to a view with --git-patch and reports empty honestly

- appends the patch to a view with --git-patch and reports empty honestly


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("appends the patch to a view with --git-patch and reports empty honestly")
val root = _repo("combined")
file_write("{root}/c.txt", "c1\n")
scv_snapshot_with_identity(root, _no_hints())
val clean = scv_diff_views(root, "raw", true)
expect(clean).to_contain("git-patch")
expect(clean).to_contain("(empty)")
file_write("{root}/c.txt", "c1\nc2\n")
val dirty = scv_diff_views(root, "raw", true)
expect(dirty).to_contain("view=raw")
expect(dirty).to_contain("git-patch")
expect(dirty).to_contain("+c2\n")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-THREE-VIEW-DIFF-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ca2cec88f78987305bcda0f141627c910d08db960a3f483e599e6347ec568bb3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca2cec88f78987305bcda0f141627c910d08db960a3f483e599e6347ec568bb3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca2cec88f78987305bcda0f141627c910d08db960a3f483e599e6347ec568bb3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_three_view_diff_spec.spl
mirror: doc/06_spec/integration/app/scv_three_view_diff_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_three_view_diff_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_three_view_diff_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_three_view_diff_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_three_view_diff_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an unknown view name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_three_view_diff_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders raw, syntax, entity, and semantic sections from one comparison' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_three_view_diff_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'labels the syntax view with structural_source provenance' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
