# dbfs_mvcc_visibility_spec

> Verifies the dbfs mvcc visibility behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_mvcc_visibility_spec

Verifies the dbfs mvcc visibility behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_mvcc_visibility_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the dbfs mvcc visibility behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### MvccHeader

#### creates with xmin set

- Verify: creates with xmin set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_MVCC_VISIBILITY-001
step("Verify: creates with xmin set")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val h = MvccHeader.create(10)
expect h.xmin == 10
expect h.xmax == 0
```

</details>

#### marks deleted with xmax

- Verify: marks deleted with xmax


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_MVCC_VISIBILITY-001
step("Verify: marks deleted with xmax")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var h = MvccHeader.create(10)
h.mark_deleted(20)
expect h.xmax == 20
```

</details>

### MvccTuple

#### creates tuple with data

- Verify: creates tuple with data


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_MVCC_VISIBILITY-001
step("Verify: creates tuple with data")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val t = MvccTuple.create(5, "hello")
expect t.header.xmin == 5
expect t.data == "hello"
```

</details>

#### marks tuple deleted

- Verify: marks tuple deleted


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_MVCC_VISIBILITY-001
step("Verify: marks tuple deleted")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var t = MvccTuple.create(5, "hello")
t.delete(10)
expect t.header.xmax == 10
```

</details>

### MvccSnapshot

#### detects active transactions

- Verify: detects active transactions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_MVCC_VISIBILITY-001
step("Verify: detects active transactions")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [3, 5, 7])
expect snap.is_txn_active(3) == true
expect snap.is_txn_active(5) == true
expect snap.is_txn_active(2) == false
```

</details>

### MVCC Visibility

#### committed insert is visible

- Verify: committed insert is visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_MVCC_VISIBILITY-001
step("Verify: committed insert is visible")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val tuple = MvccTuple.create(1, "row1")
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [])
expect mvcc_is_visible(tuple, snap) == true
```

</details>

#### active insert is not visible

- Verify: active insert is not visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_MVCC_VISIBILITY-001
step("Verify: active insert is not visible")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val tuple = MvccTuple.create(5, "row1")
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [5])
expect mvcc_is_visible(tuple, snap) == false
```

</details>

#### future insert is not visible

- Verify: future insert is not visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_MVCC_VISIBILITY-001
step("Verify: future insert is not visible")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val tuple = MvccTuple.create(15, "row1")
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [])
expect mvcc_is_visible(tuple, snap) == false
```

</details>

#### deleted tuple is not visible

- Verify: deleted tuple is not visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_MVCC_VISIBILITY-001
step("Verify: deleted tuple is not visible")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var tuple = MvccTuple.create(1, "row1")
tuple.delete(5)
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [])
expect mvcc_is_visible(tuple, snap) == false
```

</details>

#### tuple deleted by active txn is still visible

- Verify: tuple deleted by active txn is still visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_MVCC_VISIBILITY-001
step("Verify: tuple deleted by active txn is still visible")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var tuple = MvccTuple.create(1, "row1")
tuple.delete(5)
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [5])
expect mvcc_is_visible(tuple, snap) == true
```

</details>

### MvccTable

#### inserts and scans tuples

- Verify: inserts and scans tuples


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_MVCC_VISIBILITY-001
step("Verify: inserts and scans tuples")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var table = MvccTable.new()
table.insert(1, "row1")
table.insert(1, "row2")
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [])
val visible = table.scan(snap)
expect visible.len() == 2
```

</details>

#### counts visible tuples

- Verify: counts visible tuples


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_MVCC_VISIBILITY-001
step("Verify: counts visible tuples")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var table = MvccTable.new()
table.insert(1, "a")
table.insert(1, "b")
table.insert(5, "c")
val snap = MvccSnapshot(xmin: 1, xmax: 4, active_txns: [])
expect table.count_visible(snap) == 2
```

</details>

#### delete hides tuple from scan

- Verify: delete hides tuple from scan


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_MVCC_VISIBILITY-001
step("Verify: delete hides tuple from scan")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var table = MvccTable.new()
table.insert(1, "row1")
table.insert(1, "row2")
table.delete_matching(2, "row1")
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [])
expect table.count_visible(snap) == 1
```

</details>

### MvccTxnManager

#### assigns incrementing txn ids

- Verify: assigns incrementing txn ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_MVCC_VISIBILITY-001
step("Verify: assigns incrementing txn ids")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var mgr = MvccTxnManager.new()
val h1 = mgr.begin()
val h2 = mgr.begin()
expect h2.txn_id > h1.txn_id
```

</details>

#### tracks active transactions in snapshot

- Verify: tracks active transactions in snapshot


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_MVCC_VISIBILITY-001
step("Verify: tracks active transactions in snapshot")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var mgr = MvccTxnManager.new()
val h1 = mgr.begin()
val h2 = mgr.begin()
val snap = mgr.snapshot()
expect snap.is_txn_active(h1.txn_id) == true
expect snap.is_txn_active(h2.txn_id) == true
```

</details>

#### commit removes from active

- Verify: commit removes from active


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_MVCC_VISIBILITY-001
step("Verify: commit removes from active")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var mgr = MvccTxnManager.new()
val h1 = mgr.begin()
mgr.commit(h1.txn_id)
val snap = mgr.snapshot()
expect snap.is_txn_active(h1.txn_id) == false
expect mgr.get_status(h1.txn_id) == "committed"
```

</details>

#### abort removes from active

- Verify: abort removes from active


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-DBFS_DBFS_MVCC_VISIBILITY-001
step("Verify: abort removes from active")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var mgr = MvccTxnManager.new()
val h1 = mgr.begin()
mgr.abort(h1.txn_id)
val snap = mgr.snapshot()
expect snap.is_txn_active(h1.txn_id) == false
expect mgr.get_status(h1.txn_id) == "aborted"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c36daeaf4143e1cecf3bd4cdf8b0564a8d46815dea145f93adf387368312abae`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c36daeaf4143e1cecf3bd4cdf8b0564a8d46815dea145f93adf387368312abae`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c36daeaf4143e1cecf3bd4cdf8b0564a8d46815dea145f93adf387368312abae`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/storage/dbfs/dbfs_mvcc_visibility_spec.spl
mirror: doc/06_spec/02_integration/storage/dbfs/dbfs_mvcc_visibility_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/storage/dbfs/dbfs_mvcc_visibility_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/storage/dbfs/dbfs_mvcc_visibility_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/storage/dbfs/dbfs_mvcc_visibility_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
