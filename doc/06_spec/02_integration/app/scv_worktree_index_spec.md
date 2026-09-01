# scv_worktree_index_spec

> Purpose: This spec proves the SCV-IMPL-E-05 persistent binary worktree index

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_worktree_index_spec

Purpose: This spec proves the SCV-IMPL-E-05 persistent binary worktree index

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/scv_worktree_index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves the SCV-IMPL-E-05 persistent binary worktree index
(`src/lib/scv/worktree_index.spl`): entries keyed by path carrying mode,
size, mtime/ctime, BOTH ContentIds (worktree + repository), FileId, a
per-entry clock, and header-level dirty/ignore generations; serialized as a
length-prefixed BINARY record file so paths containing pipes, tabs, or
spaces round-trip exactly (lifting the pipe-delimited path limits).
NOTE (honest dependency): plan row E-05 depends on B-04 (metadata DB, another
lane). This index is its own binary store with a clean load/save/upsert/get/
remove surface the B-04 DB migration can adopt; it does NOT use the DB yet.
Audience: Maintainers of the SCV working-copy layer.

## Scenarios

### scv persistent binary worktree index (E-05)

#### upserts, gets, and removes entries keyed by path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Insert two entries, replace one, remove one
   - Expected: idx.entries.len() equals `2`
   - Expected: got.size equals `99`
   - Expected: got.clock equals `3`
   - Expected: idx.entries.len() equals `1`
   - Expected: scv_wtindex_get(idx, "src/b.spl").path equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-WORKTREE-INDEX-001
step("Insert two entries, replace one, remove one")
var idx = scv_wtindex_new()
idx = scv_wtindex_upsert(idx, _entry("src/a.spl", 10, 1))
idx = scv_wtindex_upsert(idx, _entry("src/b.spl", 20, 2))
idx = scv_wtindex_upsert(idx, _entry("src/a.spl", 99, 3))
expect(idx.entries.len()).to_equal(2)
val got = scv_wtindex_get(idx, "src/a.spl")
expect(got.size).to_equal(99)
expect(got.clock).to_equal(3)
idx = scv_wtindex_remove(idx, "src/b.spl")
expect(idx.entries.len()).to_equal(1)
expect(scv_wtindex_get(idx, "src/b.spl").path).to_equal("")
```

</details>

#### round-trips the full record through the binary file format

- Save then load; every field of every entry must survive
   - Expected: scv_wtindex_save("{root}/index.bin", idx) is true
   - Expected: back.entries.len() equals `2`
   - Expected: e.mode equals `420`
   - Expected: e.size equals `11`
   - Expected: e.mtime_ms equals `1700000000000`
   - Expected: e.ctime_ms equals `1700000000001`
   - Expected: e.worktree_content_id equals `sha256_wt_11`
   - Expected: e.repository_content_id equals `sha256_repo_11`
   - Expected: e.file_id equals `fid_5`
   - Expected: e.clock equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-WORKTREE-INDEX-001
step("Save then load; every field of every entry must survive")
val root = _root("rt")
var idx = scv_wtindex_new()
idx = scv_wtindex_upsert(idx, _entry("src/one.spl", 11, 5))
idx = scv_wtindex_upsert(idx, _entry("doc/two.md", 22, 6))
expect(scv_wtindex_save("{root}/index.bin", idx)).to_equal(true)
val back = scv_wtindex_load("{root}/index.bin")
expect(back.entries.len()).to_equal(2)
val e = scv_wtindex_get(back, "src/one.spl")
expect(e.mode).to_equal(420)
expect(e.size).to_equal(11)
expect(e.mtime_ms).to_equal(1700000000000)
expect(e.ctime_ms).to_equal(1700000000001)
expect(e.worktree_content_id).to_equal("sha256_wt_11")
expect(e.repository_content_id).to_equal("sha256_repo_11")
expect(e.file_id).to_equal("fid_5")
expect(e.clock).to_equal(5)
dir_remove_all(root)
```

</details>

#### lifts pipe-delimited path limits: pipes, tabs, and spaces round-trip

- Paths hostile to line/pipe formats must survive byte-exactly
   - Expected: scv_wtindex_save("{root}/index.bin", idx) is true
   - Expected: back.entries.len() equals `3`
   - Expected: scv_wtindex_get(back, p).path equals `p`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-WORKTREE-INDEX-001
step("Paths hostile to line/pipe formats must survive byte-exactly")
val root = _root("hostile")
val hostile = ["dir/with pipe|in|name.txt", "dir/with\ttab.txt", "dir/with space.txt"]
var idx = scv_wtindex_new()
var clock = 1
for p in hostile:
    idx = scv_wtindex_upsert(idx, _entry(p, 7, clock))
    clock = clock + 1
expect(scv_wtindex_save("{root}/index.bin", idx)).to_equal(true)
val back = scv_wtindex_load("{root}/index.bin")
expect(back.entries.len()).to_equal(3)
for p in hostile:
    expect(scv_wtindex_get(back, p).path).to_equal(p)
dir_remove_all(root)
```

</details>

#### persists header-level dirty and ignore generations

- Bump both generations, save, load, verify
   - Expected: scv_wtindex_save("{root}/index.bin", idx) is true
   - Expected: back.dirty_generation equals `2`
   - Expected: back.ignore_generation equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-WORKTREE-INDEX-001
step("Bump both generations, save, load, verify")
val root = _root("gens")
var idx = scv_wtindex_new()
idx = scv_wtindex_bump_dirty_gen(idx)
idx = scv_wtindex_bump_dirty_gen(idx)
idx = scv_wtindex_bump_ignore_gen(idx)
idx = scv_wtindex_upsert(idx, _entry("src/x.spl", 1, 1))
expect(scv_wtindex_save("{root}/index.bin", idx)).to_equal(true)
val back = scv_wtindex_load("{root}/index.bin")
expect(back.dirty_generation).to_equal(2)
expect(back.ignore_generation).to_equal(1)
dir_remove_all(root)
```

</details>

#### loading a missing or corrupt index yields an empty fresh index

- Missing file and bad magic both fail closed to empty
   - Expected: missing.entries.len() equals `0`
   - Expected: missing.dirty_generation equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-WORKTREE-INDEX-001
step("Missing file and bad magic both fail closed to empty")
val root = _root("bad")
val missing = scv_wtindex_load("{root}/nope.bin")
expect(missing.entries.len()).to_equal(0)
expect(missing.dirty_generation).to_equal(0)
dir_remove_all(root)
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

- `REQ-SCV-WORKTREE-INDEX-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9dfe4c03348cb1ad4b1a6f3c8fb11fc54d493bb54396936de10249431ffe11dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9dfe4c03348cb1ad4b1a6f3c8fb11fc54d493bb54396936de10249431ffe11dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9dfe4c03348cb1ad4b1a6f3c8fb11fc54d493bb54396936de10249431ffe11dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/02_integration/app/scv_worktree_index_spec.spl
mirror: doc/06_spec/02_integration/app/scv_worktree_index_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/scv_worktree_index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/scv_worktree_index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/scv_worktree_index_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/scv_worktree_index_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'upserts, gets, and removes entries keyed by path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/scv_worktree_index_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips the full record through the binary file format' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/scv_worktree_index_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lifts pipe-delimited path limits: pipes, tabs, and spaces round-trip' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
