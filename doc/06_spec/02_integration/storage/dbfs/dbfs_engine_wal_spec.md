# dbfs_engine_wal_spec

> DBFS WAL Specification

<!-- sdn-diagram:id=dbfs_engine_wal_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_engine_wal_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_engine_wal_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_engine_wal_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_engine_wal_spec

DBFS WAL Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_engine_wal_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS WAL Specification

Verifies write-ahead log append, flush, durable LSN tracking,
and recovery cursor positioning:
  1. append returns monotonically increasing LSN
  2. durable_lsn advances after flush
  3. recovery cursor starts at intent_log_head
  4. appended record readable before flush
  5. flush is idempotent

## Scenarios

### DBFS WAL — append
_Append contract: monotonic LSNs, readable records._

#### first append returns LSN > 0

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wal = DbfsWal.new()
val rec = WalRecord(txn_id: 1, record_type: WAL_RECORD_COMMIT, payload: "")
val lsn = wal.append(rec).unwrap()
expect(lsn > 0).to_equal(true)
```

</details>

#### successive appends produce strictly increasing LSNs

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wal = DbfsWal.new()
val rec1 = WalRecord(txn_id: 1, record_type: WAL_RECORD_COMMIT, payload: "a")
val rec2 = WalRecord(txn_id: 2, record_type: WAL_RECORD_COMMIT, payload: "b")
val lsn1 = wal.append(rec1).unwrap()
val lsn2 = wal.append(rec2).unwrap()
expect(lsn2 > lsn1).to_equal(true)
```

</details>

#### appended record is readable by LSN before flush

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wal = DbfsWal.new()
val rec = WalRecord(txn_id: 3, record_type: WAL_RECORD_COMMIT, payload: "hello")
val lsn = wal.append(rec).unwrap()
val got = wal.read_record(lsn).unwrap()
expect(got.txn_id).to_equal(3)
```

</details>

### DBFS WAL — flush and durable LSN
_Flush advances durable_lsn._

#### durable_lsn is 0 before any flush

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wal = DbfsWal.new()
expect(wal.durable_lsn()).to_equal(0)
```

</details>

#### durable_lsn equals tail_lsn after flush

1. wal flush
   - Expected: wal.durable_lsn() equals `lsn.value`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wal = DbfsWal.new()
val rec = WalRecord(txn_id: 1, record_type: WAL_RECORD_COMMIT, payload: "")
val lsn = wal.append(rec).unwrap()
wal.flush().unwrap()
expect(wal.durable_lsn()).to_equal(lsn.value)
```

</details>

#### flush is idempotent

1. wal append

2. wal flush
   - Expected: r.is_ok() is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wal = DbfsWal.new()
val rec = WalRecord(txn_id: 1, record_type: WAL_RECORD_COMMIT, payload: "")
wal.append(rec).unwrap()
wal.flush().unwrap()
val r = wal.flush()
expect(r.is_ok()).to_equal(true)
```

</details>

### DBFS WAL — recovery cursor
_Recovery cursor starts at intent_log_head._

#### recovery_cursor starts at intent_log_head after flush

1. wal append

2. wal flush
   - Expected: cursor.start_lsn() equals `head`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wal = DbfsWal.new()
val rec = WalRecord(txn_id: 10, record_type: WAL_RECORD_COMMIT, payload: "")
wal.append(rec).unwrap()
wal.flush().unwrap()
val head = wal.intent_log_head()
val cursor = wal.recovery_cursor()
expect(cursor.start_lsn()).to_equal(head)
```

</details>

#### recovery cursor iterates all committed records

1. wal append

2. wal append

3. wal flush
   - Expected: records.len() equals `2`


<details>
<summary>Executable SPipe</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wal = DbfsWal.new()
wal.append(WalRecord(txn_id: 1, record_type: WAL_RECORD_COMMIT, payload: "a")).unwrap()
wal.append(WalRecord(txn_id: 2, record_type: WAL_RECORD_COMMIT, payload: "b")).unwrap()
wal.flush().unwrap()
val cursor = wal.recovery_cursor()
val records = cursor.collect_committed().unwrap()
expect(records.len()).to_equal(2)
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
