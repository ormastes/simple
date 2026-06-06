# Dbfs Nvme Callback Specification

> 1. var dev =  make device

<!-- sdn-diagram:id=dbfs_nvme_callback_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_nvme_callback_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_nvme_callback_spec -> std
dbfs_nvme_callback_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_nvme_callback_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Nvme Callback Specification

## Scenarios

### DBFS intent_log NVMe-backed callbacks

#### records persist through flush and survive reopen

1. var dev =  make device

2. intent register persist callback

3. intent set block device

4. var log = SharedIntentLog new persistent
   - Expected: r1.is_ok() is true
   - Expected: r2.is_ok() is true

5. var reopened = SharedIntentLog reopen
   - Expected: scanned.is_ok() is true
   - Expected: recs.len() as i64 equals `2`
   - Expected: recs[0].txn_id equals `100`
   - Expected: recs[0].lsn equals `1`
   - Expected: recs[0].committed is true
   - Expected: recs[1].txn_id equals `101`
   - Expected: recs[1].committed is false

6. intent clear persist callback


<details>
<summary>Executable SPipe</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device("intent1")
intent_register_persist_callback("arena:META_DURABLE")
intent_set_block_device(dev, 0)
var log = SharedIntentLog.new_persistent()
val r1 = log.append(IntentLogRecord(txn_id: 100, lsn: 1, committed: true))
expect(r1.is_ok()).to_equal(true)
val r2 = log.append(IntentLogRecord(txn_id: 101, lsn: 2, committed: false))
expect(r2.is_ok()).to_equal(true)
val _ = log.flush()
val _ = log.close()
var reopened = SharedIntentLog.reopen()
val scanned = reopened.scan_all()
expect(scanned.is_ok()).to_equal(true)
val recs = scanned.unwrap()
expect(recs.len() as i64).to_equal(2)
expect(recs[0].txn_id).to_equal(100)
expect(recs[0].lsn).to_equal(1)
expect(recs[0].committed).to_equal(true)
expect(recs[1].txn_id).to_equal(101)
expect(recs[1].committed).to_equal(false)
intent_clear_persist_callback()
```

</details>

#### committed records filter correctly after device reopen

1. var dev =  make device

2. intent register persist callback

3. intent set block device

4. var log = SharedIntentLog new persistent

5. var reopened = SharedIntentLog reopen
   - Expected: committed.is_ok() is true
   - Expected: crecs.len() as i64 equals `2`
   - Expected: crecs[0].txn_id equals `200`
   - Expected: crecs[1].txn_id equals `202`

6. intent clear persist callback


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device("intent2")
intent_register_persist_callback("arena:META_DURABLE")
intent_set_block_device(dev, 0)
var log = SharedIntentLog.new_persistent()
val _ = log.append(IntentLogRecord(txn_id: 200, lsn: 1, committed: true))
val _ = log.append(IntentLogRecord(txn_id: 201, lsn: 2, committed: false))
val _ = log.append(IntentLogRecord(txn_id: 202, lsn: 3, committed: true))
val _ = log.flush()
val _ = log.close()
var reopened = SharedIntentLog.reopen()
val committed = reopened.scan_committed()
expect(committed.is_ok()).to_equal(true)
val crecs = committed.unwrap()
expect(crecs.len() as i64).to_equal(2)
expect(crecs[0].txn_id).to_equal(200)
expect(crecs[1].txn_id).to_equal(202)
intent_clear_persist_callback()
```

</details>

### DBFS checkpoint_ring NVMe-backed callbacks

#### ring slots persist through write and survive reopen

1. var dev =  make device

2. ring register persist callback

3. ring set block device

4. var ring = SharedCheckpointRing new with size
   - Expected: w1.is_ok() is true
   - Expected: w2.is_ok() is true

5. var reopened = SharedCheckpointRing reopen
   - Expected: s0.is_ok() is true
   - Expected: slot0.gen equals `1`
   - Expected: slot0.clean is true
   - Expected: slot0.btree_root_page equals `42`
   - Expected: s1.is_ok() is true
   - Expected: slot1.gen equals `2`
   - Expected: slot1.btree_root_page equals `84`

6. ring clear persist callback


<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device("ring1")
ring_register_persist_callback("arena:META_DURABLE")
ring_set_block_device(dev, 32)
var ring = SharedCheckpointRing.new_with_size(16)
val w1 = ring.write_slot(0, RingSlot(gen: 1, clean: true, btree_root_page: 42))
expect(w1.is_ok()).to_equal(true)
val w2 = ring.write_slot(1, RingSlot(gen: 2, clean: true, btree_root_page: 84))
expect(w2.is_ok()).to_equal(true)
val _ = ring.close()
var reopened = SharedCheckpointRing.reopen()
val s0 = reopened.read_slot(0)
expect(s0.is_ok()).to_equal(true)
val slot0 = s0.unwrap()
expect(slot0.gen).to_equal(1)
expect(slot0.clean).to_equal(true)
expect(slot0.btree_root_page).to_equal(42)
val s1 = reopened.read_slot(1)
expect(s1.is_ok()).to_equal(true)
val slot1 = s1.unwrap()
expect(slot1.gen).to_equal(2)
expect(slot1.btree_root_page).to_equal(84)
ring_clear_persist_callback()
```

</details>

#### latest_clean finds correct slot after device reopen

1. var dev =  make device

2. ring register persist callback

3. ring set block device

4. var ring = SharedCheckpointRing new with size

5. var reopened = SharedCheckpointRing reopen
   - Expected: s.gen equals `30`
   - Expected: s.btree_root_page equals `300`

6. fail

7. ring clear persist callback


<details>
<summary>Executable SPipe</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var dev = _make_device("ring2")
ring_register_persist_callback("arena:META_DURABLE")
ring_set_block_device(dev, 32)
var ring = SharedCheckpointRing.new_with_size(16)
val _ = ring.write_slot(0, RingSlot(gen: 10, clean: true, btree_root_page: 100))
val _ = ring.write_slot(1, RingSlot(gen: 20, clean: false, btree_root_page: 200))
val _ = ring.write_slot(2, RingSlot(gen: 30, clean: true, btree_root_page: 300))
val _ = ring.close()
var reopened = SharedCheckpointRing.reopen()
val latest = reopened.latest_clean()
match latest:
    case Some(s):
        expect(s.gen).to_equal(30)
        expect(s.btree_root_page).to_equal(300)
    case None:
        fail("checkpoint ring latest_clean returned None")
ring_clear_persist_callback()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_nvme_callback_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- DBFS intent_log NVMe-backed callbacks
- DBFS checkpoint_ring NVMe-backed callbacks

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
