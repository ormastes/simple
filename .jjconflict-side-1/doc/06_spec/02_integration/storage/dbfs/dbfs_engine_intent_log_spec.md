# dbfs_engine_intent_log_spec

> DBFS Intent Log Disk Persistence Specification

<!-- sdn-diagram:id=dbfs_engine_intent_log_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_engine_intent_log_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_engine_intent_log_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_engine_intent_log_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_engine_intent_log_spec

DBFS Intent Log Disk Persistence Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_engine_intent_log_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS Intent Log Disk Persistence Specification

Verifies R1 HIGH-risk gap: intent-log records survive a simulated remount.
The in-memory placeholder must be replaced by disk persistence to META_DURABLE.

  1. records written before simulated crash are present after remount
  2. remount reads the correct tail LSN
  3. committed records are replayed; uncommitted are skipped
  4. intent-log head pointer is durable across remount

## Scenarios

### DBFS Intent Log — disk persistence after remount
_Records written before remount survive and are replayed._

#### records are present after remount (not lost in-memory)

1. log append
2. log flush
3. log close
   - Expected: records.len() equals `1`
   - Expected: records[0].txn_id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = IntentLog.new_persistent()
val rec = IntentLogRecord(txn_id: 1, lsn: 100, committed: true)
log.append(rec).unwrap()
log.flush().unwrap()
log.close().unwrap()
val log2 = IntentLog.reopen()
val records = log2.scan_all().unwrap()
expect(records.len()).to_equal(1)
expect(records[0].txn_id).to_equal(1)
```

</details>

#### tail LSN is correct after remount

1. log append
2. log flush
3. log close
   - Expected: head.tail_lsn equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = IntentLog.new_persistent()
log.append(IntentLogRecord(txn_id: 1, lsn: 42, committed: true)).unwrap()
log.flush().unwrap()
log.close().unwrap()
val log2 = IntentLog.reopen()
val head = log2.head().unwrap()
expect(head.tail_lsn).to_equal(42)
```

</details>

### DBFS Intent Log — committed vs uncommitted replay
_Committed records replayed; uncommitted skipped._

#### only committed records appear in replay after remount

1. log append
2. log append
3. log flush
4. log close
   - Expected: committed.len() equals `1`
   - Expected: committed[0].txn_id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = IntentLog.new_persistent()
log.append(IntentLogRecord(txn_id: 1, lsn: 10, committed: true)).unwrap()
log.append(IntentLogRecord(txn_id: 2, lsn: 11, committed: false)).unwrap()
log.flush().unwrap()
log.close().unwrap()
val log2 = IntentLog.reopen()
val committed = log2.scan_committed().unwrap()
expect(committed.len()).to_equal(1)
expect(committed[0].txn_id).to_equal(1)
```

</details>

#### uncommitted record count after remount is zero in committed scan

1. log append
2. log flush
3. log close
   - Expected: committed.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = IntentLog.new_persistent()
log.append(IntentLogRecord(txn_id: 5, lsn: 20, committed: false)).unwrap()
log.flush().unwrap()
log.close().unwrap()
val log2 = IntentLog.reopen()
val committed = log2.scan_committed().unwrap()
expect(committed.len()).to_equal(0)
```

</details>

### DBFS Intent Log — storage class
_Intent log must write to META_DURABLE arena._

#### intent log uses META_DURABLE storage class

1. log append
2. log flush
   - Expected: sc equals `StorageClass.MetaDurable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = IntentLog.new_persistent()
log.append(IntentLogRecord(txn_id: 1, lsn: 1, committed: true)).unwrap()
log.flush().unwrap()
val sc = log.last_write_storage_class()
expect(sc).to_equal(StorageClass.MetaDurable)
```

</details>

### DBFS Intent Log — head pointer durability
_Head pointer survives remount._

#### intent_log_head pointer matches after remount

1. log append
2. log flush
3. log close
   - Expected: head_after.tail_lsn equals `head_before.tail_lsn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log = IntentLog.new_persistent()
log.append(IntentLogRecord(txn_id: 7, lsn: 77, committed: true)).unwrap()
log.flush().unwrap()
val head_before = log.head().unwrap()
log.close().unwrap()
val log2 = IntentLog.reopen()
val head_after = log2.head().unwrap()
expect(head_after.tail_lsn).to_equal(head_before.tail_lsn)
```

</details>

### DBFS Intent Log — callback persistence
_When callback is registered, writes go through the callback path._

#### callback path persists records across reopen

1. intent clear persist callback
2. intent register persist callback
   - Expected: intent_is_callback_registered() is true
3. log append
4. log append
5. log flush
6. log close
   - Expected: intent_cb_record_count() equals `2`
   - Expected: records.len() equals `2`
   - Expected: committed.len() equals `1`
   - Expected: committed[0].txn_id equals `3`
7. intent clear persist callback


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
intent_clear_persist_callback()
intent_register_persist_callback("arena:META_DURABLE")
expect(intent_is_callback_registered()).to_equal(true)
val log = IntentLog.new_persistent()
log.append(IntentLogRecord(txn_id: 3, lsn: 30, committed: true)).unwrap()
log.append(IntentLogRecord(txn_id: 4, lsn: 40, committed: false)).unwrap()
log.flush().unwrap()
log.close().unwrap()
expect(intent_cb_record_count()).to_equal(2)
val log2 = IntentLog.reopen()
val records = log2.scan_all().unwrap()
expect(records.len()).to_equal(2)
val committed = log2.scan_committed().unwrap()
expect(committed.len()).to_equal(1)
expect(committed[0].txn_id).to_equal(3)
intent_clear_persist_callback()
```

</details>

#### callback registration is clearable

1. intent register persist callback
   - Expected: intent_is_callback_registered() is true
2. intent clear persist callback
   - Expected: intent_is_callback_registered() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
intent_register_persist_callback("test")
expect(intent_is_callback_registered()).to_equal(true)
intent_clear_persist_callback()
expect(intent_is_callback_registered()).to_equal(false)
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
