# Storage Shared Facade Specification

> <details>

<!-- sdn-diagram:id=storage_shared_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=storage_shared_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

storage_shared_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=storage_shared_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Storage Shared Facade Specification

## Scenarios

### gc_async_mut storage shared facade

#### re-exports wal and btree primitives

- var wal = SharedWal new
   - Expected: lsn.value equals `1`
   - Expected: wal.read_record(Lsn(value: 1)).unwrap().payload equals `payload`
   - Expected: wal.flush_wal().is_ok() is true
   - Expected: wal.get_durable_lsn().value equals `1`
   - Expected: WAL_RECORD_COMMIT equals `3`
- var tree = BTree<text> new
   - Expected: tree.insert(BTreeKey(a: 1, b: 2), "value").is_ok() is true
   - Expected: found equals `value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var wal = SharedWal.new()
val lsn = wal.append(WalRecord(txn_id: 7, record_type: WAL_RECORD_DATA, payload: "payload")).unwrap()
expect(lsn.value).to_equal(1)
expect(wal.read_record(Lsn(value: 1)).unwrap().payload).to_equal("payload")
expect(wal.flush_wal().is_ok()).to_equal(true)
expect(wal.get_durable_lsn().value).to_equal(1)
expect(WAL_RECORD_COMMIT).to_equal(3)

var tree = BTree<text>.new(2)
expect(tree.insert(BTreeKey(a: 1, b: 2), "value").is_ok()).to_equal(true)
val found = tree.lookup(BTreeKey(a: 1, b: 2)).unwrap()
expect(found).to_equal("value")
```

</details>

#### re-exports checkpoint ring and intent log persistence helpers

- ring clear persist callback
- ring register persist callback
   - Expected: ring_is_callback_registered() is true
   - Expected: ring_persist_callback_tag() equals `facade-ring`
- var ring = SharedCheckpointRing new with size
   - Expected: ring.write_slot(0, RingSlot(slot_gen: 2, clean: true, btree_root_page: 99)).is_ok() is true
   - Expected: ring_cb_slot_count() equals `1`
   - Expected: ring.latest_clean().unwrap().btree_root_page equals `99`
- intent clear persist callback
- intent register persist callback
   - Expected: intent_is_callback_registered() is true
   - Expected: intent_persist_callback_tag() equals `facade-intent`
- var log = SharedIntentLog new persistent
   - Expected: log.append(IntentLogRecord(txn_id: 1, lsn: 5, committed: true)).is_ok() is true
- log set head
   - Expected: log.flush().is_ok() is true
   - Expected: intent_cb_record_count() equals `1`
   - Expected: log.head_pointer().tail_lsn equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
ring_clear_persist_callback()
ring_register_persist_callback("facade-ring")
expect(ring_is_callback_registered()).to_equal(true)
expect(ring_persist_callback_tag()).to_equal("facade-ring")
var ring = SharedCheckpointRing.new_with_size(4)
expect(ring.write_slot(0, RingSlot(slot_gen: 2, clean: true, btree_root_page: 99)).is_ok()).to_equal(true)
expect(ring_cb_slot_count()).to_equal(1)
expect(ring.latest_clean().unwrap().btree_root_page).to_equal(99)

intent_clear_persist_callback()
intent_register_persist_callback("facade-intent")
expect(intent_is_callback_registered()).to_equal(true)
expect(intent_persist_callback_tag()).to_equal("facade-intent")
var log = SharedIntentLog.new_persistent()
expect(log.append(IntentLogRecord(txn_id: 1, lsn: 5, committed: true)).is_ok()).to_equal(true)
log.set_head(5)
expect(log.flush().is_ok()).to_equal(true)
expect(intent_cb_record_count()).to_equal(1)
expect(log.head_pointer().tail_lsn).to_equal(5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/storage/shared/storage_shared_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut storage shared facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
