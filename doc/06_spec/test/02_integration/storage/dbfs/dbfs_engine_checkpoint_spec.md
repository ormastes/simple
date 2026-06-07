# dbfs_engine_checkpoint_spec

> DBFS Checkpoint Specification

<!-- sdn-diagram:id=dbfs_engine_checkpoint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_engine_checkpoint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_engine_checkpoint_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_engine_checkpoint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_engine_checkpoint_spec

DBFS Checkpoint Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_engine_checkpoint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS Checkpoint Specification

Verifies checkpoint atomicity and META_DURABLE storage class usage:
  1. root publication is atomic (old root visible until new succeeds)
  2. checkpoint ring keeps N previous entries
  3. META_DURABLE storage class is used for checkpoint writes
  4. partial checkpoint does not corrupt the ring

## Scenarios

### DBFS Checkpoint — atomic root publication
_Old root must remain visible until new checkpoint completes._

#### old root is readable before new checkpoint commits

1. ckpt publish
   - Expected: current.gen equals `1`
2. pending abort


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ckpt = DbfsCheckpoint.new()
val root1 = CheckpointRoot(btree_root: PageId(1), gen: 1)
ckpt.publish(root1).unwrap()
val root2 = CheckpointRoot(btree_root: PageId(2), gen: 2)
# Simulate: begin new checkpoint but do NOT commit yet
val pending = ckpt.begin_publish(root2)
val current = ckpt.current_root().unwrap()
expect(current.gen).to_equal(1)
pending.abort()
```

</details>

#### new root is visible after commit

1. ckpt publish
2. ckpt publish
   - Expected: current.gen equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ckpt = DbfsCheckpoint.new()
ckpt.publish(CheckpointRoot(btree_root: PageId(1), gen: 1)).unwrap()
ckpt.publish(CheckpointRoot(btree_root: PageId(2), gen: 2)).unwrap()
val current = ckpt.current_root().unwrap()
expect(current.gen).to_equal(2)
```

</details>

### DBFS Checkpoint — ring retention
_Ring retains published entries until the configured ring size is exceeded._

#### ring retains last 4 entries after 5 publishes

1.  publish 5 roots to ring
   - Expected: entries.len() >= 4 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Uses module-level helper: publish() write_pos mutation is lost
# between calls under interpreter value-semantics.
val ckpt = DbfsCheckpoint.new()
_publish_5_roots_to_ring()
val entries = ckpt.ring_entries().unwrap()
expect(entries.len() >= 4).to_equal(true)
```

</details>

#### ring entries still include the latest published generation after 5 publishes

1.  publish 5 roots to ring
   - Expected: found_latest is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Uses module-level helpers: write_pos + var-rebind value-semantics workarounds.
val ckpt = DbfsCheckpoint.new()
_publish_5_roots_to_ring()
val entries = ckpt.ring_entries().unwrap()
val found_latest = _entries_contain_gen(entries, 5)
expect(found_latest).to_equal(true)
```

</details>

### DBFS Checkpoint — META_DURABLE storage class
_Checkpoint writes must target META_DURABLE arena._

#### checkpoint write uses META_DURABLE storage class

1. ckpt publish
   - Expected: storage_class equals `StorageClass.MetaDurable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ckpt = DbfsCheckpoint.new()
ckpt.publish(CheckpointRoot(btree_root: PageId(1), gen: 1)).unwrap()
val storage_class = ckpt.last_write_storage_class()
expect(storage_class).to_equal(StorageClass.MetaDurable)
```

</details>

### DBFS Checkpoint — partial failure safety
_Aborting a publish leaves ring intact._

#### ring is unchanged when publish is aborted

1. ckpt publish
2. pending abort
   - Expected: current.gen equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ckpt = DbfsCheckpoint.new()
ckpt.publish(CheckpointRoot(btree_root: PageId(1), gen: 1)).unwrap()
val pending = ckpt.begin_publish(CheckpointRoot(btree_root: PageId(2), gen: 2))
pending.abort()
val current = ckpt.current_root().unwrap()
expect(current.gen).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
