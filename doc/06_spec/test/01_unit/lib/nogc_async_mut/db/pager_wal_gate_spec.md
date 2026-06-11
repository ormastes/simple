# Pager WAL-before-data Gate Specification

> Tests that pager.write_page enforces WAL-before-data at the pager layer (E5).

<!-- sdn-diagram:id=pager_wal_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pager_wal_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pager_wal_gate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pager_wal_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pager WAL-before-data Gate Specification

Tests that pager.write_page enforces WAL-before-data at the pager layer (E5).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DB-WAL-GATE |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/lib/nogc_async_mut/db/pager_wal_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that pager.write_page enforces WAL-before-data at the pager layer (E5).

Rules:
- write_page with page_lsn > wal_flushed_lsn → Err (WAL not flushed)
- write_page after WAL flush advancing flushed_lsn ≥ page_lsn → Ok
- write_page with page_lsn = 0 → Ok regardless (raw pager use, no WAL)

## Scenarios

### Pager WAL-before-data gate

#### page_lsn = 0 (no WAL context)
_write_page with page_lsn=0 always succeeds regardless of wal_flushed_lsn._

#### succeeds when page_lsn is 0 and wal_flushed_lsn is 0

- var p = DbfsPager new
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = DbfsPager.new(4)
val pid_r = p.alloc_page()
val pid = pid_r.unwrap()
val data = PageData.zeroed()
val result = p.write_page(pid, data, 0, 0)
expect(result.is_ok()).to_equal(true)
```

</details>

#### succeeds when page_lsn is 0 even if wal_flushed_lsn is behind

- var p = DbfsPager new
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = DbfsPager.new(4)
val pid_r = p.alloc_page()
val pid = pid_r.unwrap()
val data = PageData.zeroed()
# wal_flushed_lsn=0, page_lsn=0 — gate skipped
val result = p.write_page(pid, data, 0, 0)
expect(result.is_ok()).to_equal(true)
```

</details>

#### page_lsn > 0 with unflushed WAL
_write_page with page_lsn > wal_flushed_lsn returns Err._

#### returns Err when WAL not yet flushed for this page

- var p = DbfsPager new
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = DbfsPager.new(4)
val pid_r = p.alloc_page()
val pid = pid_r.unwrap()
val data = PageData.zeroed()
# page_lsn=5, wal_flushed_lsn=3 → WAL behind → Err
val result = p.write_page(pid, data, 5, 3)
expect(result.is_err()).to_equal(true)
```

</details>

#### returns Err when wal_flushed_lsn is zero and page_lsn is positive

- var p = DbfsPager new
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = DbfsPager.new(4)
val pid_r = p.alloc_page()
val pid = pid_r.unwrap()
val data = PageData.zeroed()
val result = p.write_page(pid, data, 1, 0)
expect(result.is_err()).to_equal(true)
```

</details>

#### returns Err when page_lsn is one ahead of flushed_lsn

- var p = DbfsPager new
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = DbfsPager.new(4)
val pid_r = p.alloc_page()
val pid = pid_r.unwrap()
val data = PageData.zeroed()
# flushed=9, page_lsn=10 → still blocked
val result = p.write_page(pid, data, 10, 9)
expect(result.is_err()).to_equal(true)
```

</details>

#### page_lsn > 0 after WAL flush
_write_page succeeds when wal_flushed_lsn >= page_lsn._

#### succeeds when wal_flushed_lsn equals page_lsn

- var p = DbfsPager new
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = DbfsPager.new(4)
val pid_r = p.alloc_page()
val pid = pid_r.unwrap()
val data = PageData.zeroed()
# flushed=5, page_lsn=5 → exact match → Ok
val result = p.write_page(pid, data, 5, 5)
expect(result.is_ok()).to_equal(true)
```

</details>

#### succeeds when wal_flushed_lsn exceeds page_lsn

- var p = DbfsPager new
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = DbfsPager.new(4)
val pid_r = p.alloc_page()
val pid = pid_r.unwrap()
val data = PageData.zeroed()
# flushed=10, page_lsn=3 → flushed ahead → Ok
val result = p.write_page(pid, data, 3, 10)
expect(result.is_ok()).to_equal(true)
```

</details>

#### write marks page dirty after successful gated write

- var p = DbfsPager new
   - Expected: wr.is_ok() is true
   - Expected: p.is_dirty(pid) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = DbfsPager.new(4)
val pid_r = p.alloc_page()
val pid = pid_r.unwrap()
val data = PageData.zeroed()
val wr = p.write_page(pid, data, 2, 2)
expect(wr.is_ok()).to_equal(true)
expect(p.is_dirty(pid)).to_equal(true)
```

</details>

#### WAL flushed_lsn accessor
_SharedWal.flushed_lsn() returns durable_lsn._

#### flushed_lsn is 0 on fresh WAL

- var w = SharedWal new
   - Expected: w.flushed_lsn() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = SharedWal.new()
expect(w.flushed_lsn()).to_equal(0)
```

</details>

#### flushed_lsn advances after flush_wal

- var w = SharedWal new
   - Expected: w.flushed_lsn() equals `lsn.value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = SharedWal.new()
val rec = WalRecord(txn_id: 1, record_type: WAL_RECORD_DATA, payload: "d")
val lsn_r = w.append(rec)
val lsn = lsn_r.unwrap()
val _ = w.flush_wal()
expect(w.flushed_lsn()).to_equal(lsn.value)
```

</details>

#### flushed_lsn matches durable_lsn

- var w = SharedWal new
   - Expected: w.flushed_lsn() equals `w.durable_lsn()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = SharedWal.new()
val rec = WalRecord(txn_id: 1, record_type: WAL_RECORD_DATA, payload: "x")
val _ = w.append(rec)
val _ = w.flush_wal()
expect(w.flushed_lsn()).to_equal(w.durable_lsn())
```

</details>

#### end-to-end: WAL flush then pager write
_Simulates the D4 protocol: append WAL, flush WAL, then write page._

#### page write succeeds after WAL flush

- var w = SharedWal new
- var p = DbfsPager new
   - Expected: wr.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = SharedWal.new()
var p = DbfsPager.new(4)
val pid_r = p.alloc_page()
val pid = pid_r.unwrap()
# Step 3: WAL append
val rec = WalRecord(txn_id: 1, record_type: WAL_RECORD_DATA, payload: "data")
val lsn_r = w.append(rec)
val lsn = lsn_r.unwrap()
# Step 4: WAL flush
val _ = w.flush_wal()
val flushed = w.flushed_lsn()
# Step: write page with real LSNs
val data = PageData.zeroed()
val wr = p.write_page(pid, data, lsn.value, flushed)
expect(wr.is_ok()).to_equal(true)
```

</details>

#### page write fails before WAL flush

- var w = SharedWal new
- var p = DbfsPager new
   - Expected: wr.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var w = SharedWal.new()
var p = DbfsPager.new(4)
val pid_r = p.alloc_page()
val pid = pid_r.unwrap()
# Append WAL but do NOT flush
val rec = WalRecord(txn_id: 1, record_type: WAL_RECORD_DATA, payload: "data")
val lsn_r = w.append(rec)
val lsn = lsn_r.unwrap()
val flushed = w.flushed_lsn()   # still 0
val data = PageData.zeroed()
val wr = p.write_page(pid, data, lsn.value, flushed)
expect(wr.is_err()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
