# Dbfs Mvcc Visibility Specification

> Tests covering MvccHeader, MvccTuple, MvccSnapshot, MVCC Visibility, MvccTable, MvccTxnManager.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Mvcc Visibility Specification

## Scenarios

### MvccHeader

#### creates with xmin set

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates with xmin set


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates with xmin set")
val h = MvccHeader.create(10)
expect h.xmin == 10
expect h.xmax == 0
```

</details>

#### marks deleted with xmax

- marks deleted with xmax


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("marks deleted with xmax")
var h = MvccHeader.create(10)
h.mark_deleted(20)
expect h.xmax == 20
```

</details>

### MvccTuple

#### creates tuple with data

- creates tuple with data


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("creates tuple with data")
val t = MvccTuple.create(5, "hello")
expect t.header.xmin == 5
expect t.data == "hello"
```

</details>

#### marks tuple deleted

- marks tuple deleted


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("marks tuple deleted")
var t = MvccTuple.create(5, "hello")
t.delete(10)
expect t.header.xmax == 10
```

</details>

### MvccSnapshot

#### detects active transactions

- detects active transactions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("detects active transactions")
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [3, 5, 7])
expect snap.is_txn_active(3) == true
expect snap.is_txn_active(5) == true
expect snap.is_txn_active(2) == false
```

</details>

### MVCC Visibility

#### committed insert is visible

- committed insert is visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("committed insert is visible")
val tuple = MvccTuple.create(1, "row1")
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [])
expect mvcc_is_visible(tuple, snap) == true
```

</details>

#### active insert is not visible

- active insert is not visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("active insert is not visible")
val tuple = MvccTuple.create(5, "row1")
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [5])
expect mvcc_is_visible(tuple, snap) == false
```

</details>

#### future insert is not visible

- future insert is not visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("future insert is not visible")
val tuple = MvccTuple.create(15, "row1")
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [])
expect mvcc_is_visible(tuple, snap) == false
```

</details>

#### deleted tuple is not visible

- deleted tuple is not visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("deleted tuple is not visible")
var tuple = MvccTuple.create(1, "row1")
tuple.delete(5)
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [])
expect mvcc_is_visible(tuple, snap) == false
```

</details>

#### tuple deleted by active txn is still visible

- tuple deleted by active txn is still visible


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tuple deleted by active txn is still visible")
var tuple = MvccTuple.create(1, "row1")
tuple.delete(5)
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [5])
expect mvcc_is_visible(tuple, snap) == true
```

</details>

### MvccTable

#### inserts and scans tuples

- inserts and scans tuples


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("inserts and scans tuples")
var table = MvccTable.new()
table.insert(1, "row1")
table.insert(1, "row2")
val snap = MvccSnapshot(xmin: 1, xmax: 10, active_txns: [])
val visible = table.scan(snap)
expect visible.len() == 2
```

</details>

#### counts visible tuples

- counts visible tuples


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("counts visible tuples")
var table = MvccTable.new()
table.insert(1, "a")
table.insert(1, "b")
table.insert(5, "c")
val snap = MvccSnapshot(xmin: 1, xmax: 4, active_txns: [])
expect table.count_visible(snap) == 2
```

</details>

#### delete hides tuple from scan

- delete hides tuple from scan


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("delete hides tuple from scan")
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

- assigns incrementing txn ids


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("assigns incrementing txn ids")
var mgr = MvccTxnManager.new()
val h1 = mgr.begin()
val h2 = mgr.begin()
expect h2.txn_id > h1.txn_id
```

</details>

#### tracks active transactions in snapshot

- tracks active transactions in snapshot


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("tracks active transactions in snapshot")
var mgr = MvccTxnManager.new()
val h1 = mgr.begin()
val h2 = mgr.begin()
val snap = mgr.snapshot()
expect snap.is_txn_active(h1.txn_id) == true
expect snap.is_txn_active(h2.txn_id) == true
```

</details>

#### commit removes from active

- commit removes from active


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("commit removes from active")
var mgr = MvccTxnManager.new()
val h1 = mgr.begin()
mgr.commit(h1.txn_id)
val snap = mgr.snapshot()
expect snap.is_txn_active(h1.txn_id) == false
expect mgr.get_status(h1.txn_id) == "committed"
```

</details>

#### abort removes from active

- abort removes from active


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("abort removes from active")
var mgr = MvccTxnManager.new()
val h1 = mgr.begin()
mgr.abort(h1.txn_id)
val snap = mgr.snapshot()
expect snap.is_txn_active(h1.txn_id) == false
expect mgr.get_status(h1.txn_id) == "aborted"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/integration/storage/dbfs/dbfs_mvcc_visibility_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MvccHeader, MvccTuple, MvccSnapshot, MVCC Visibility, MvccTable, MvccTxnManager.
- MvccHeader
- MvccTuple
- MvccSnapshot
- MVCC Visibility
- MvccTable
- MvccTxnManager

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3289b71685dc33738292813f339c09625796761850c5278f67848cb798810c9a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3289b71685dc33738292813f339c09625796761850c5278f67848cb798810c9a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3289b71685dc33738292813f339c09625796761850c5278f67848cb798810c9a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/storage/dbfs/dbfs_mvcc_visibility_spec.spl
mirror: doc/06_spec/integration/storage/dbfs/dbfs_mvcc_visibility_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/dbfs/dbfs_mvcc_visibility_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/dbfs/dbfs_mvcc_visibility_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/dbfs/dbfs_mvcc_visibility_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates with xmin set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_mvcc_visibility_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks deleted with xmax' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_mvcc_visibility_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates tuple with data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
