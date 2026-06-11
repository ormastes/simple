# Dbfs Recovery Namespace Facade Specification

> 1. var tree = NsBTree new

<!-- sdn-diagram:id=dbfs_recovery_namespace_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_recovery_namespace_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_recovery_namespace_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_recovery_namespace_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dbfs Recovery Namespace Facade Specification

## Scenarios

### nogc_async_mut DBFS recovery namespace facade

#### re-exports namespace, intent-log, and recovery contracts

1. var tree = NsBTree new
   - Expected: tree.insert(NsDentryKey(parent_ino: 1, name_hash: 22), NsIno(value: 2)).is_ok() is true
   - Expected: tree.lookup(NsDentryKey(parent_ino: 1, name_hash: 22)).unwrap().value equals `2`
   - Expected: log.append(IntentLogRecord(txn_id: 1, lsn: 10, committed: true)).is_ok() is true
   - Expected: log.append(IntentLogRecord(txn_id: 2, lsn: 11, committed: false)).is_ok() is true
   - Expected: log.flush().is_ok() is true
   - Expected: log.scan_committed().unwrap().len() equals `1`
2. recovery clear callbacks
3. recovery register discard cb
4. recovery register checkpoint cb
5. replicas: [SuperblockReplica
6. FaultWalEntry
7. FaultWalEntry
   - Expected: recovered.superblock_gen equals `3`
   - Expected: recovered.replayed_txn_ids.len() equals `1`
   - Expected: recovery_get_discarded_ids()[0] equals `99`
   - Expected: recovery_get_checkpoint_gen() equals `4`
8. recovery clear callbacks


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tree = NsBTree.new()
expect(tree.insert(NsDentryKey(parent_ino: 1, name_hash: 22), NsIno(value: 2)).is_ok()).to_equal(true)
expect(tree.lookup(NsDentryKey(parent_ino: 1, name_hash: 22)).unwrap().value).to_equal(2)

val log = IntentLog.new_persistent()
expect(log.append(IntentLogRecord(txn_id: 1, lsn: 10, committed: true)).is_ok()).to_equal(true)
expect(log.append(IntentLogRecord(txn_id: 2, lsn: 11, committed: false)).is_ok()).to_equal(true)
expect(log.flush().is_ok()).to_equal(true)
expect(log.scan_committed().unwrap().len()).to_equal(1)

recovery_clear_callbacks()
recovery_register_discard_cb("arena")
recovery_register_checkpoint_cb("checkpoint")
val device = FaultDevice(
    replicas: [SuperblockReplica(generation: 3, crc_valid: true)],
    wal_entries: [
        FaultWalEntry(txn_id: 10, committed: true, lsn: 1),
        FaultWalEntry(txn_id: 11, committed: false, lsn: 2)
    ],
    orphan_arenas: [99],
    fault_after: -1,
    last_clean_gen: 3
)
val recovered = DbfsRecovery.recover(device).unwrap()
expect(recovered.superblock_gen).to_equal(3)
expect(recovered.replayed_txn_ids.len()).to_equal(1)
expect(recovery_get_discarded_ids()[0]).to_equal(99)
expect(recovery_get_checkpoint_gen()).to_equal(4)
recovery_clear_callbacks()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/db/dbfs_engine/dbfs_recovery_namespace_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- nogc_async_mut DBFS recovery namespace facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
