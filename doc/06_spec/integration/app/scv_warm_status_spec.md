# scv_warm_status_spec

> Purpose: This spec proves SCV-IMPL-E-06, warm status with zero payload reads

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_warm_status_spec

Purpose: This spec proves SCV-IMPL-E-06, warm status with zero payload reads

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_warm_status_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV-IMPL-E-06, warm status with zero payload reads
(`src/lib/scv/warm_status.spl`). A warm, clean `status` over the persistent
worktree index (E-05) costs O(events): with no events it performs ZERO stat
calls, ZERO content reads and no parsing — proven behaviourally by clobbering
a file on disk with no event for it and observing that status still reports
clean. One changed file costs at most ONE stable content read (a
FileBuffer read, MIG-19), and a modified event whose stat still matches the
index costs a stat but no read. Every I/O is counted by a REAL counter
incremented at the single choke point that performs the syscall — the spec
asserts on those counters, not on a mock claim. The E-01 `fswatch_scan`
sha256-every-file path is never used on the warm path.
Audience: Maintainers of the SCV working-copy layer.

## Scenarios

### scv warm status zero-payload-reads (E-06)

#### cold build reads each file exactly once and records stat + content id

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Build the index from disk; 3 files => 3 reads, 3 entries
   - Expected: built.index.entries.len() equals `3`
   - Expected: built.io.content_reads equals `3`
   - Expected: e.size equals `6`
   - Expected: e.worktree_content_id.starts_with("sha256_") is true
   - Expected: e.repository_content_id equals `e.worktree_content_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-WARM-STATUS-001
step("Build the index from disk; 3 files => 3 reads, 3 entries")
val root = _root("cold")
val built = scv_warm_index_build(root)
expect(built.index.entries.len()).to_equal(3)
expect(built.io.content_reads).to_equal(3)
val e = scv_wtindex_get(built.index, "src/a.spl")
expect(e.size).to_equal(6)
expect(e.worktree_content_id.starts_with("sha256_")).to_equal(true)
expect(e.repository_content_id).to_equal(e.worktree_content_id)
dir_remove_all(root)
```

</details>

#### warm clean status with no events is O(events): 0 stats, 0 reads, clean

- Clobber a file WITHOUT an event; warm status must not notice it
   - Expected: res.io.stat_calls equals `0`
   - Expected: res.io.content_reads equals `0`
   - Expected: res.io.parses equals `0`
   - Expected: scv_warm_status_lines(res) equals `clean\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-WARM-STATUS-001
step("Clobber a file WITHOUT an event; warm status must not notice it")
val root = _root("warm")
val built = scv_warm_index_build(root)
file_write("{root}/src/b.spl", "beta changed on disk, no event\n")
val res = scv_warm_status(root, built.index, [])
expect(res.io.stat_calls).to_equal(0)
expect(res.io.content_reads).to_equal(0)
expect(res.io.parses).to_equal(0)
expect(scv_warm_status_lines(res)).to_equal("clean\n")
dir_remove_all(root)
```

</details>

#### one changed file costs at most one stable content read

- Modify a.spl (size changes), deliver ONE modified event
   - Expected: res.io.content_reads equals `1`
   - Expected: res.io.parses equals `0`
   - Expected: scv_warm_status_lines(res) equals `M src/a.spl\n`
- The index now carries the new worktree content id and size
   - Expected: e.size equals `16`
   - Expected: e.worktree_content_id != e.repository_content_id is true
- A second status with the same event re-stats but does NOT re-read
   - Expected: again.io.stat_calls > 0 is true
   - Expected: again.io.content_reads equals `0`
   - Expected: scv_warm_status_lines(again) equals `M src/a.spl\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-WARM-STATUS-001
step("Modify a.spl (size changes), deliver ONE modified event")
val root = _root("one")
val built = scv_warm_index_build(root)
file_write("{root}/src/a.spl", "alpha rewritten\n")
val res = scv_warm_status(root, built.index, [_ev(1, "modified", "{root}/src/a.spl")])
expect(res.io.content_reads).to_equal(1)
expect(res.io.parses).to_equal(0)
expect(scv_warm_status_lines(res)).to_equal("M src/a.spl\n")
step("The index now carries the new worktree content id and size")
val e = scv_wtindex_get(res.index, "src/a.spl")
expect(e.size).to_equal(16)
expect(e.worktree_content_id != e.repository_content_id).to_equal(true)
step("A second status with the same event re-stats but does NOT re-read")
val again = scv_warm_status(root, res.index, [_ev(2, "modified", "{root}/src/a.spl")])
expect(again.io.stat_calls > 0).to_equal(true)
expect(again.io.content_reads).to_equal(0)
expect(scv_warm_status_lines(again)).to_equal("M src/a.spl\n")
dir_remove_all(root)
```

</details>

#### a spurious modified event with unchanged stat costs a stat and zero reads

- Deliver a modified event for a file that did not change
   - Expected: res.io.stat_calls > 0 is true
   - Expected: res.io.content_reads equals `0`
   - Expected: scv_warm_status_lines(res) equals `clean\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-WARM-STATUS-001
step("Deliver a modified event for a file that did not change")
val root = _root("spurious")
val built = scv_warm_index_build(root)
val res = scv_warm_status(root, built.index, [_ev(1, "modified", "{root}/src/b.spl")])
expect(res.io.stat_calls > 0).to_equal(true)
expect(res.io.content_reads).to_equal(0)
expect(scv_warm_status_lines(res)).to_equal("clean\n")
dir_remove_all(root)
```

</details>

#### created and deleted events update the index with zero reads for deletes

- Create c.spl (1 read), delete README.md (0 reads)
   - Expected: res.io.content_reads equals `1`
   - Expected: scv_warm_status_lines(res) equals `A src/c.spl\nD README.md\n`
   - Expected: res.index.entries.len() equals `3`
   - Expected: scv_wtindex_get(res.index, "README.md").path equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-WARM-STATUS-001
step("Create c.spl (1 read), delete README.md (0 reads)")
val root = _root("cd")
val built = scv_warm_index_build(root)
file_write("{root}/src/c.spl", "gamma\n")
file_delete("{root}/README.md")
val evs = [_ev(1, "created", "{root}/src/c.spl"), _ev(2, "deleted", "{root}/README.md")]
val res = scv_warm_status(root, built.index, evs)
expect(res.io.content_reads).to_equal(1)
expect(scv_warm_status_lines(res)).to_equal("A src/c.spl\nD README.md\n")
expect(res.index.entries.len()).to_equal(3)
expect(scv_wtindex_get(res.index, "README.md").path).to_equal("")
dir_remove_all(root)
```

</details>

#### duplicate events for one path are coalesced to a single read

- Five modified events on the same path => 1 read
   - Expected: res.io.content_reads equals `1`
   - Expected: scv_warm_status_lines(res) equals `M src/a.spl\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SCV-WARM-STATUS-001
step("Five modified events on the same path => 1 read")
val root = _root("dup")
val built = scv_warm_index_build(root)
file_write("{root}/src/a.spl", "alpha again\n")
var evs: [FsWatchEvent] = []
var i = 1
while i <= 5:
    evs.push(_ev(i, "modified", "{root}/src/a.spl"))
    i = i + 1
val res = scv_warm_status(root, built.index, evs)
expect(res.io.content_reads).to_equal(1)
expect(scv_warm_status_lines(res)).to_equal("M src/a.spl\n")
dir_remove_all(root)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-WARM-STATUS-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e25b46db2e1bc97697b6c75a3cb4257bee7d8ee576940d5a0416ff7be0a405f4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e25b46db2e1bc97697b6c75a3cb4257bee7d8ee576940d5a0416ff7be0a405f4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e25b46db2e1bc97697b6c75a3cb4257bee7d8ee576940d5a0416ff7be0a405f4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_warm_status_spec.spl
mirror: doc/06_spec/integration/app/scv_warm_status_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/integration/app/scv_warm_status_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_warm_status_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_warm_status_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/scv_warm_status_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_warm_status_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cold build reads each file exactly once and records stat + content id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_warm_status_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warm clean status with no events is O(events): 0 stats, 0 reads, clean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_warm_status_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'one changed file costs at most one stable content read' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
