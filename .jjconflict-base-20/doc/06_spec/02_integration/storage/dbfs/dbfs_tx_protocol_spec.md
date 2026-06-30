# dbfs_tx_protocol_spec

> DBFS Transaction Protocol Specification

<!-- sdn-diagram:id=dbfs_tx_protocol_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dbfs_tx_protocol_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dbfs_tx_protocol_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dbfs_tx_protocol_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# dbfs_tx_protocol_spec

DBFS Transaction Protocol Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/storage/dbfs/dbfs_tx_protocol_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

DBFS Transaction Protocol Specification

Verifies the 6-step write path (D4):
  1. data blobs written before metadata pages
  2. metadata pages written before WAL append
  3. WAL appended before flush
  4. flush is the only fsync point (DURABLE_GROUP_COMMIT)
  5. root CAS after flush
  6. partially-published txn is invisible to readers
  7. DURABLE_GROUP_COMMIT batches one fsync per commit

## Scenarios

### DBFS Tx Protocol — 6-step write order
_Steps must occur in the prescribed order._

#### data step precedes metadata step

1. txn write data
2. txn write metadata private
3. txn append wal
4. txn flush wal
5. txn publish root
6. txn commit
   - Expected: order.index_of(TxnStep.Data) < order.index_of(TxnStep.MetadataPrivate) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = make_driver()
val txn = driver.begin_txn()
val steps = txn.observe_steps()
txn.write_data("hello").unwrap()
txn.write_metadata_private().unwrap()
txn.append_wal().unwrap()
txn.flush_wal().unwrap()
txn.publish_root().unwrap()
txn.commit().unwrap()
val order = steps.order()
expect(order.index_of(TxnStep.Data) < order.index_of(TxnStep.MetadataPrivate)).to_equal(true)
```

</details>

#### metadata step precedes WAL append

1. txn write data
2. txn write metadata private
3. txn append wal
4. txn flush wal
5. txn publish root
6. txn commit
   - Expected: order.index_of(TxnStep.MetadataPrivate) < order.index_of(TxnStep.WalAppend) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = make_driver()
val txn = driver.begin_txn()
val steps = txn.observe_steps()
txn.write_data("x").unwrap()
txn.write_metadata_private().unwrap()
txn.append_wal().unwrap()
txn.flush_wal().unwrap()
txn.publish_root().unwrap()
txn.commit().unwrap()
val order = steps.order()
expect(order.index_of(TxnStep.MetadataPrivate) < order.index_of(TxnStep.WalAppend)).to_equal(true)
```

</details>

#### WAL append precedes flush

1. txn write data
2. txn write metadata private
3. txn append wal
4. txn flush wal
5. txn publish root
6. txn commit
   - Expected: order.index_of(TxnStep.WalAppend) < order.index_of(TxnStep.Flush) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = make_driver()
val txn = driver.begin_txn()
val steps = txn.observe_steps()
txn.write_data("y").unwrap()
txn.write_metadata_private().unwrap()
txn.append_wal().unwrap()
txn.flush_wal().unwrap()
txn.publish_root().unwrap()
txn.commit().unwrap()
val order = steps.order()
expect(order.index_of(TxnStep.WalAppend) < order.index_of(TxnStep.Flush)).to_equal(true)
```

</details>

#### flush precedes root publish

1. txn write data
2. txn write metadata private
3. txn append wal
4. txn flush wal
5. txn publish root
6. txn commit
   - Expected: order.index_of(TxnStep.Flush) < order.index_of(TxnStep.Publish) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = make_driver()
val txn = driver.begin_txn()
val steps = txn.observe_steps()
txn.write_data("z").unwrap()
txn.write_metadata_private().unwrap()
txn.append_wal().unwrap()
txn.flush_wal().unwrap()
txn.publish_root().unwrap()
txn.commit().unwrap()
val order = steps.order()
expect(order.index_of(TxnStep.Flush) < order.index_of(TxnStep.Publish)).to_equal(true)
```

</details>

### DBFS Tx Protocol — visibility
_Partially-published txn is invisible to concurrent readers._

#### uncommitted txn data is invisible to a second reader

1. driver mkdir
2. txn write data
3. txn write metadata private
4. txn append wal
   - Expected: stat.is_err() is true
5. txn abort


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = make_driver()
driver.mkdir("/tmp", 0o755).unwrap()
val txn = driver.begin_txn()
txn.write_data("secret").unwrap()
txn.write_metadata_private().unwrap()
txn.append_wal().unwrap()
# Do NOT flush or publish — txn is in-flight
val stat = driver.stat("/tmp/secret_file")
expect(stat.is_err()).to_equal(true)
txn.abort()
```

</details>

### DBFS Tx Protocol — DURABLE_GROUP_COMMIT
_Only one fsync per commit boundary._

#### two concurrent txns share one flush call

1. txn1 write data
2. txn2 write data
3. txn1 append wal
4. txn2 append wal
5. driver group commit
   - Expected: flush_count_after - flush_count_before equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = make_driver()
val flush_count_before = driver.flush_call_count()
val txn1 = driver.begin_txn()
val txn2 = driver.begin_txn()
txn1.write_data("a").unwrap()
txn2.write_data("b").unwrap()
txn1.append_wal().unwrap()
txn2.append_wal().unwrap()
driver.group_commit().unwrap()
val flush_count_after = driver.flush_call_count()
expect(flush_count_after - flush_count_before).to_equal(1)
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
