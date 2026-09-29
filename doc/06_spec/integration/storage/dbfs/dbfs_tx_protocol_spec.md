# dbfs_tx_protocol_spec

> DBFS Transaction Protocol Specification

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
| Source | `test/integration/storage/dbfs/dbfs_tx_protocol_spec.spl` |
| Updated | 2026-08-26 |
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

#### data step precedes metadata step

- data step precedes metadata step
   - Expected: order.index_of(TxnStep.Data) < order.index_of(TxnStep.MetadataPrivate) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("data step precedes metadata step")
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

- metadata step precedes WAL append
   - Expected: order.index_of(TxnStep.MetadataPrivate) < order.index_of(TxnStep.WalAppend) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("metadata step precedes WAL append")
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

- WAL append precedes flush
   - Expected: order.index_of(TxnStep.WalAppend) < order.index_of(TxnStep.Flush) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("WAL append precedes flush")
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

- flush precedes root publish
   - Expected: order.index_of(TxnStep.Flush) < order.index_of(TxnStep.Publish) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("flush precedes root publish")
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

- uncommitted txn data is invisible to a second reader
   - Expected: stat.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("uncommitted txn data is invisible to a second reader")
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

- two concurrent txns share one flush call
   - Expected: flush_count_after - flush_count_before equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("two concurrent txns share one flush call")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cc49f45a3ca898db4714b0e2f86a264cf8f70c567ca2098393367d4f702f6711`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cc49f45a3ca898db4714b0e2f86a264cf8f70c567ca2098393367d4f702f6711`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cc49f45a3ca898db4714b0e2f86a264cf8f70c567ca2098393367d4f702f6711`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/integration/storage/dbfs/dbfs_tx_protocol_spec.spl
mirror: doc/06_spec/integration/storage/dbfs/dbfs_tx_protocol_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/storage/dbfs/dbfs_tx_protocol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/storage/dbfs/dbfs_tx_protocol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/storage/dbfs/dbfs_tx_protocol_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/storage/dbfs/dbfs_tx_protocol_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'data step precedes metadata step' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_tx_protocol_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'metadata step precedes WAL append' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/storage/dbfs/dbfs_tx_protocol_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'WAL append precedes flush' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
