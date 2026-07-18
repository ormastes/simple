# dbfs_recovery_spec

> DBFS Recovery Specification

<!-- sdn-diagram:id=dbfs_recovery_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_recovery_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_recovery_spec -> std
dbfs_recovery_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_recovery_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_recovery_spec

DBFS Recovery Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_recovery_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS Recovery Specification

Verifies 5-step D5 recovery model using the power-cut harness:
  1. best-of-3 superblock replicas: highest gen + valid CRC wins
  2. only committed WAL records are replayed
  3. orphan arenas are reclaimed via arena_discard
  4. clean mount-generation is written after recovery
  5. partially-written superblock is rejected

## Scenarios

### DBFS Recovery — superblock replica selection
_Best-of-3 replicas: highest gen with valid CRC._

#### picks replica with highest valid gen

1. harness write replica

2. harness write replica

3. harness write replica
   - Expected: result.superblock_gen equals `5`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harness = PowerCutHarness.new()
harness.write_replica(0, SuperblockReplica(generation: 3, crc_valid: true))
harness.write_replica(1, SuperblockReplica(generation: 5, crc_valid: true))
harness.write_replica(2, SuperblockReplica(generation: 4, crc_valid: true))
val result = DbfsRecovery.recover(harness.device()).unwrap()
expect(result.superblock_gen).to_equal(5)
```

</details>

#### skips replica with invalid CRC

1. harness write replica

2. harness write replica

3. harness write replica
   - Expected: result.superblock_gen equals `3`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harness = PowerCutHarness.new()
harness.write_replica(0, SuperblockReplica(generation: 10, crc_valid: false))
harness.write_replica(1, SuperblockReplica(generation: 3, crc_valid: true))
harness.write_replica(2, SuperblockReplica(generation: 2, crc_valid: true))
val result = DbfsRecovery.recover(harness.device()).unwrap()
expect(result.superblock_gen).to_equal(3)
```

</details>

### DBFS Recovery — WAL replay
_Only committed records are replayed._

#### committed record is replayed after power-cut

1. harness inject fault

2. harness write wal record

3. harness mark committed
   - Expected: result.replayed_txn_ids contains `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harness = PowerCutHarness.new()
harness.inject_fault(FaultPoint.AfterWalFlush)
harness.write_wal_record(WalRecord(txn_id: 1, record_type: WAL_RECORD_COMMIT, payload: "inode=42"))
harness.mark_committed(txn_id: 1)
val result = DbfsRecovery.recover(harness.device()).unwrap()
expect(result.replayed_txn_ids.contains(1)).to_equal(true)
```

</details>

#### uncommitted record is NOT replayed

1. harness inject fault

2. harness write wal record
   - Expected: result.replayed_txn_ids does not contain `7`


<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harness = PowerCutHarness.new()
harness.inject_fault(FaultPoint.AfterWalAppend)
harness.write_wal_record(WalRecord(txn_id: 7, record_type: WAL_RECORD_COMMIT, payload: "inode=99"))
# txn_id 7 never got a COMMIT record
val result = DbfsRecovery.recover(harness.device()).unwrap()
expect(result.replayed_txn_ids.contains(7)).to_equal(false)
```

</details>

### DBFS Recovery — orphan reclamation
_Orphan arenas are discarded after crash._

#### orphan arenas are reclaimed via arena_discard

1. harness inject fault

2. harness mark orphan arena
   - Expected: result.discarded_orphan_arena_ids contains `99`


<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harness = PowerCutHarness.new()
harness.inject_fault(FaultPoint.AfterDataWrite)
harness.mark_orphan_arena(arena_id: 99)
val result = DbfsRecovery.recover(harness.device()).unwrap()
expect(result.discarded_orphan_arena_ids.contains(99)).to_equal(true)
```

</details>

### DBFS Recovery — clean mount generation
_After recovery, a new clean checkpoint entry is written._

#### recovery writes a new clean checkpoint slot

1. harness inject fault
   - Expected: result.clean_mount_gen > 0 is true


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harness = PowerCutHarness.new()
harness.inject_fault(FaultPoint.AfterWalFlush)
val result = DbfsRecovery.recover(harness.device()).unwrap()
expect(result.clean_mount_gen > 0).to_equal(true)
```

</details>

#### mount generation increments from previous clean checkpoint

1. harness set last clean gen
   - Expected: result.clean_mount_gen equals `9`


<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val harness = PowerCutHarness.new()
harness.set_last_clean_gen(g: 8)
val result = DbfsRecovery.recover(harness.device()).unwrap()
expect(result.clean_mount_gen).to_equal(9)
```

</details>

### DBFS Recovery — callback-based side effects
_When callbacks are registered, recovery routes discard and checkpoint through them._

#### discard callback receives orphan arena IDs

1. recovery clear callbacks

2. recovery register discard cb

3. harness mark orphan arena

4. harness mark orphan arena
   - Expected: discarded contains `42`
   - Expected: discarded contains `77`

5. recovery clear callbacks


<details>
<summary>Executable SPipe</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
recovery_clear_callbacks()
recovery_register_discard_cb("arena:META_DURABLE")
val harness = PowerCutHarness.new()
harness.mark_orphan_arena(arena_id: 42)
harness.mark_orphan_arena(arena_id: 77)
val result = DbfsRecovery.recover(harness.device()).unwrap()
val discarded = recovery_get_discarded_ids()
expect(discarded.contains(42)).to_equal(true)
expect(discarded.contains(77)).to_equal(true)
recovery_clear_callbacks()
```

</details>

#### checkpoint callback receives mount generation

1. recovery clear callbacks

2. recovery register checkpoint cb

3. harness set last clean gen
   - Expected: cp_gen equals `6`

4. recovery clear callbacks


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
recovery_clear_callbacks()
recovery_register_checkpoint_cb("arena:META_DURABLE")
val harness = PowerCutHarness.new()
harness.set_last_clean_gen(g: 5)
val result = DbfsRecovery.recover(harness.device()).unwrap()
val cp_gen = recovery_get_checkpoint_gen()
expect(cp_gen).to_equal(6)
recovery_clear_callbacks()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
