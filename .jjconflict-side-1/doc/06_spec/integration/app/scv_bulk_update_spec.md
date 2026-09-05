# scv_bulk_update_spec

> Purpose: This spec proves SCV-IMPL-E-07, the bulk-update generation

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_bulk_update_spec

Purpose: This spec proves SCV-IMPL-E-07, the bulk-update generation

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_bulk_update_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves SCV-IMPL-E-07, the bulk-update generation
(`src/lib/scv/bulk_update.spl`). A checkout / rebase / branch-switch marks a
generation on the worktree index (E-05 dirty generation bump) and on the
coalescer (E-04 bulk hold); every per-file event delivered while the bulk
operation is active is DEFERRED — no stat, no read — and duplicate events per
path are folded. `scv_bulk_end` reconciles ONCE through the E-06 warm-status
path: reads are bounded by the number of distinct surviving paths, the index
generation advances by exactly one per bulk operation, and reconciled entries
carry that generation. Nested/duplicate begins do not double-bump.
Audience: Maintainers of the SCV working-copy layer.

## Scenarios

### scv bulk-update generation (E-07)

#### begin marks a generation on the index and holds the coalescer

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- checkout begin => dirty generation +1, coalescer bulk-held
   - Expected: scv_bulk_active(bulk) is true
   - Expected: bulk.index.dirty_generation equals `gen0 + 1`
   - Expected: bulk.generation equals `gen0 + 1`
   - Expected: bulk.reason equals `checkout`
- A vcs-class event added to the held coalescer never settles by time
   - Expected: released.len() equals `0`
   - Expected: scv_coalesce_pending_count(c2) equals `1`
- A nested begin does not double-bump the generation
   - Expected: bulk.index.dirty_generation equals `gen0 + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-BULK-UPDATE-001, REQ-SSPEC-INTEGRATION
step("checkout begin => dirty generation +1, coalescer bulk-held")
val root = _root("begin")
val built = scv_warm_index_build(root)
val gen0 = built.index.dirty_generation
var bulk = scv_bulk_begin(built.index, scv_coalesce_open(50, 200), "checkout")
expect(scv_bulk_active(bulk)).to_equal(true)
expect(bulk.index.dirty_generation).to_equal(gen0 + 1)
expect(bulk.generation).to_equal(gen0 + 1)
expect(bulk.reason).to_equal("checkout")
step("A vcs-class event added to the held coalescer never settles by time")
bulk.coalescer = scv_coalesce_add(bulk.coalescer, _ev(1, "modified", "{root}/src/a.spl"), "vcs", 0)
val (c2, released) = scv_coalesce_flush_ready(bulk.coalescer, 100000)
expect(released.len()).to_equal(0)
expect(scv_coalesce_pending_count(c2)).to_equal(1)
step("A nested begin does not double-bump the generation")
bulk = scv_bulk_begin(bulk.index, bulk.coalescer, "rebase")
expect(bulk.index.dirty_generation).to_equal(gen0 + 1)
dir_remove_all(root)
```

</details>

#### defers per-file events with zero I/O and folds duplicates per path

- 60 events across 3 paths while bulk is active => 3 deferred, 0 reads
   - Expected: scv_bulk_deferred_count(bulk) equals `3`
   - Expected: bulk.io.stat_calls equals `0`
   - Expected: bulk.io.content_reads equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-BULK-UPDATE-001
step("60 events across 3 paths while bulk is active => 3 deferred, 0 reads")
val root = _root("defer")
val built = scv_warm_index_build(root)
var bulk = scv_bulk_begin(built.index, scv_coalesce_open(50, 200), "rebase")
var seq = 1
while seq <= 60:
    val p = if seq % 3 == 0: "a.spl" elif seq % 3 == 1: "b.spl" else: "c.spl"
    bulk = scv_bulk_defer(bulk, _ev(seq, "modified", "{root}/src/{p}"))
    seq = seq + 1
expect(scv_bulk_deferred_count(bulk)).to_equal(3)
expect(bulk.io.stat_calls).to_equal(0)
expect(bulk.io.content_reads).to_equal(0)
dir_remove_all(root)
```

</details>

#### end reconciles once: reads bounded by distinct paths, entries carry the generation

- branch-switch rewrites a and b, deletes c, then end
   - Expected: scv_bulk_active(res.bulk) is false
   - Expected: scv_bulk_deferred_count(res.bulk) equals `0`
   - Expected: res.status.io.content_reads equals `2`
   - Expected: scv_warm_status_lines(res.status) equals `M src/a.spl\nM src/b.spl\nD src/c.spl\n`
   - Expected: scv_wtindex_get(res.status.index, "src/a.spl").dirty_gen equals `gen`
   - Expected: scv_wtindex_get(res.status.index, "src/b.spl").dirty_gen equals `gen`
   - Expected: scv_wtindex_get(res.status.index, "src/c.spl").path equals ``
- Untouched entries keep their pre-bulk generation
   - Expected: res.status.index.dirty_generation equals `gen`
- Ending again with nothing deferred is a no-op with zero I/O
   - Expected: again.status.io.content_reads equals `0`
   - Expected: again.status.io.stat_calls equals `0`
   - Expected: scv_warm_status_lines(again.status) equals `clean\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-BULK-UPDATE-001
step("branch-switch rewrites a and b, deletes c, then end")
val root = _root("end")
val built = scv_warm_index_build(root)
var bulk = scv_bulk_begin(built.index, scv_coalesce_open(50, 200), "branch-switch")
file_write("{root}/src/a.spl", "alpha from other branch\n")
file_write("{root}/src/b.spl", "beta from other branch\n")
file_delete("{root}/src/c.spl")
var seq = 1
while seq <= 10:
    bulk = scv_bulk_defer(bulk, _ev(seq, "modified", "{root}/src/a.spl"))
    bulk = scv_bulk_defer(bulk, _ev(seq + 100, "modified", "{root}/src/b.spl"))
    seq = seq + 1
bulk = scv_bulk_defer(bulk, _ev(500, "deleted", "{root}/src/c.spl"))
val res = scv_bulk_end(root, bulk)
expect(scv_bulk_active(res.bulk)).to_equal(false)
expect(scv_bulk_deferred_count(res.bulk)).to_equal(0)
expect(res.status.io.content_reads).to_equal(2)
expect(scv_warm_status_lines(res.status)).to_equal("M src/a.spl\nM src/b.spl\nD src/c.spl\n")
val gen = res.bulk.generation
expect(scv_wtindex_get(res.status.index, "src/a.spl").dirty_gen).to_equal(gen)
expect(scv_wtindex_get(res.status.index, "src/b.spl").dirty_gen).to_equal(gen)
expect(scv_wtindex_get(res.status.index, "src/c.spl").path).to_equal("")
step("Untouched entries keep their pre-bulk generation")
expect(res.status.index.dirty_generation).to_equal(gen)
step("Ending again with nothing deferred is a no-op with zero I/O")
val again = scv_bulk_end(root, res.bulk)
expect(again.status.io.content_reads).to_equal(0)
expect(again.status.io.stat_calls).to_equal(0)
expect(scv_warm_status_lines(again.status)).to_equal("clean\n")
dir_remove_all(root)
```

</details>

#### created-then-deleted inside one generation annihilates to a delete with zero reads

- tmp file created and removed during checkout never gets read
   - Expected: res.status.io.content_reads equals `0`
   - Expected: scv_warm_status_lines(res.status) equals `clean\n`
   - Expected: res.status.index.entries.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-BULK-UPDATE-001
step("tmp file created and removed during checkout never gets read")
val root = _root("annihilate")
val built = scv_warm_index_build(root)
var bulk = scv_bulk_begin(built.index, scv_coalesce_open(50, 200), "checkout")
bulk = scv_bulk_defer(bulk, _ev(1, "created", "{root}/src/tmp.spl"))
bulk = scv_bulk_defer(bulk, _ev(2, "deleted", "{root}/src/tmp.spl"))
val res = scv_bulk_end(root, bulk)
expect(res.status.io.content_reads).to_equal(0)
expect(scv_warm_status_lines(res.status)).to_equal("clean\n")
expect(res.status.index.entries.len()).to_equal(3)
dir_remove_all(root)
```

</details>

#### two consecutive bulk operations advance the generation by exactly one each

- checkout then rebase => gen +1, +1
   - Expected: first.bulk.generation equals `gen0 + 1`
   - Expected: second.bulk.generation equals `gen0 + 2`
   - Expected: second.status.index.dirty_generation equals `gen0 + 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SCV-BULK-UPDATE-001
step("checkout then rebase => gen +1, +1")
val root = _root("twice")
val built = scv_warm_index_build(root)
val gen0 = built.index.dirty_generation
var bulk = scv_bulk_begin(built.index, scv_coalesce_open(50, 200), "checkout")
val first = scv_bulk_end(root, bulk)
expect(first.bulk.generation).to_equal(gen0 + 1)
bulk = scv_bulk_begin(first.status.index, first.bulk.coalescer, "rebase")
val second = scv_bulk_end(root, bulk)
expect(second.bulk.generation).to_equal(gen0 + 2)
expect(second.status.index.dirty_generation).to_equal(gen0 + 2)
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

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-BULK-UPDATE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4d9ad592e9f29ad8e54df208df91b120da0fe1f80dc2617a83030808f2c1dd27`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4d9ad592e9f29ad8e54df208df91b120da0fe1f80dc2617a83030808f2c1dd27`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4d9ad592e9f29ad8e54df208df91b120da0fe1f80dc2617a83030808f2c1dd27`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/scv_bulk_update_spec.spl
mirror: doc/06_spec/integration/app/scv_bulk_update_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_bulk_update_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_bulk_update_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_bulk_update_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/scv_bulk_update_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'begin marks a generation on the index and holds the coalescer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_bulk_update_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defers per-file events with zero I/O and folds duplicates per path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_bulk_update_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'end reconciles once: reads bounded by distinct paths, entries carry the generation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
