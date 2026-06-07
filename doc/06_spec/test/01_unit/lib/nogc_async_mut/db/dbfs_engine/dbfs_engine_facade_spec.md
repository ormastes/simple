# Dbfs Engine Facade Specification

> 1. var txn = DbfsTxn new

<!-- sdn-diagram:id=dbfs_engine_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_engine_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_engine_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_engine_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Engine Facade Specification

## Scenarios

### nogc_async_mut DBFS engine facade

#### re-exports transaction, inline-data, and WAL contracts

1. var txn = DbfsTxn new
   - Expected: txn.write_data("abc").is_ok() is true
   - Expected: txn.write_metadata_private().is_ok() is true
   - Expected: txn.append_wal().is_ok() is true
   - Expected: txn.flush_wal().is_ok() is true
   - Expected: txn.publish_root().is_ok() is true
   - Expected: txn.commit().is_ok() is true
   - Expected: txn.status equals `TXN_STATUS_COMMITTED`
   - Expected: order.index_of(TxnStep.Data) equals `0`
   - Expected: order.index_of(TxnStep.Commit) > order.index_of(TxnStep.WalFlush) is true
   - Expected: decoded.data[1] equals `0x42`
2. var store = InlineDataStore new
   - Expected: store.put(9, [0x41, 0x42]) is true
   - Expected: data.len() as i64 equals `2`
3. fail
   - Expected: WAL_RECORD_DATA != WAL_RECORD_COMMIT is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var txn = DbfsTxn.new(TxnId.null())
expect(txn.write_data("abc").is_ok()).to_equal(true)
expect(txn.write_metadata_private().is_ok()).to_equal(true)
expect(txn.append_wal().is_ok()).to_equal(true)
expect(txn.flush_wal().is_ok()).to_equal(true)
expect(txn.publish_root().is_ok()).to_equal(true)
expect(txn.commit().is_ok()).to_equal(true)
expect(txn.status).to_equal(TXN_STATUS_COMMITTED)
val order = txn.observe_steps().order()
expect(order.index_of(TxnStep.Data)).to_equal(0)
expect(order.index_of(TxnStep.Commit) > order.index_of(TxnStep.WalFlush)).to_equal(true)

val entry = InlineEntry(ino_id: 9, data: [0x41, 0x42], size: 2)
val encoded = serialize_inline_entry(entry)
val decoded = deserialize_inline_entry(encoded)
expect(decoded.data[1]).to_equal(0x42)
var store = InlineDataStore.new(INLINE_THRESHOLD)
expect(store.put(9, [0x41, 0x42])).to_equal(true)
match resolve_read_source(9, 2, store):
    case ReadSource.Inline(data):
        expect(data.len() as i64).to_equal(2)
    case ReadSource.Extent:
        fail("small inline payload resolved to extent")
expect(WAL_RECORD_DATA != WAL_RECORD_COMMIT).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_engine_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut DBFS engine facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
