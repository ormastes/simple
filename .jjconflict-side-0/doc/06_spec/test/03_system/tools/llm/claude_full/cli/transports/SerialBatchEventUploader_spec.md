# Claude Full Serial Batch Event Uploader

> Checks ordered batching, retry, backpressure, byte limits, and close accounting.

<!-- sdn-diagram:id=SerialBatchEventUploader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=SerialBatchEventUploader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

SerialBatchEventUploader_spec -> std
SerialBatchEventUploader_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=SerialBatchEventUploader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Serial Batch Event Uploader

Checks ordered batching, retry, backpressure, byte limits, and close accounting.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/transports/SerialBatchEventUploader_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks ordered batching, retry, backpressure, byte limits, and close accounting.

## Scenarios

### Claude full SerialBatchEventUploader

#### should enqueue and send batches serially

- Enqueue three events with max batch size two
- uploader enqueue
- uploader flushSuccess
   - Expected: uploader.sentBatches.len() equals `2`
   - Expected: uploader.firstSentBatchText() equals `a,b`
   - Expected: uploader.pendingCount() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Enqueue three events with max batch size two")
val uploader = SerialBatchEventUploader.new(SerialUploaderConfig.new(2, 10))
uploader.enqueue(["a", "b", "c"])
uploader.flushSuccess()
expect(uploader.sentBatches.len()).to_equal(2)
expect(uploader.firstSentBatchText()).to_equal("a,b")
expect(uploader.pendingCount()).to_equal(0)
```

</details>

#### should apply backpressure when queue would exceed capacity

- Enqueue more events than the queue allows
- uploader enqueue
- uploader enqueueOne
   - Expected: uploader.pendingCount() equals `2`
   - Expected: uploader.backpressureResolvers equals `1`
- uploader flushSuccess
   - Expected: uploader.backpressureResolvers equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Enqueue more events than the queue allows")
val uploader = SerialBatchEventUploader.new(SerialUploaderConfig.new(2, 2))
uploader.enqueue(["a", "b"])
uploader.enqueueOne("c")
expect(uploader.pendingCount()).to_equal(2)
expect(uploader.backpressureResolvers).to_equal(1)
uploader.flushSuccess()
expect(uploader.backpressureResolvers).to_equal(0)
```

</details>

#### should honor max batch bytes and drop unserializable items

- Take a byte-limited batch
- uploader enqueue
   - Expected: joinText(batch) equals `abc`
   - Expected: joinText(uploader.pending) equals `de,fg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Take a byte-limited batch")
val uploader = serialUploaderWithByteLimit(5, 7, 10)
uploader.enqueue(["abc", "de", "UNSERIALIZABLE", "fg"])
val batch = uploader.takeBatch()
expect(joinText(batch)).to_equal("abc")
expect(joinText(uploader.pending)).to_equal("de,fg")
```

</details>

#### should requeue failed batches and compute retry delay

- Fail the first batch and observe front requeue
- uploader enqueue
   - Expected: delay equals `110`
   - Expected: joinText(uploader.pending) equals `a,b,c`
   - Expected: uploader.sleepResolve is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fail the first batch and observe front requeue")
val config = serialUploaderConfig(2, 10, 100, 500, 50)
val uploader = SerialBatchEventUploader.new(config)
uploader.enqueue(["a", "b", "c"])
val delay = uploader.failOnce(0, 10)
expect(delay).to_equal(110)
expect(joinText(uploader.pending)).to_equal("a,b,c")
expect(uploader.sleepResolve).to_equal(true)
```

</details>

#### should clamp retry-after delays and drop after failure cap

- Use server retry-after and then hit the drop cap
   - Expected: retryDelay(config, 4, 1000, 99) equals `525`
- uploader enqueue
- uploader failUntilDropped
   - Expected: uploader.droppedBatchCount() equals `1`
   - Expected: uploader.dropLog[0] equals `2:2`
   - Expected: joinText(uploader.pending) equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use server retry-after and then hit the drop cap")
val config = SerialUploaderConfig(maxBatchSize: 2, maxBatchBytes: 0, maxQueueSize: 10, baseDelayMs: 100, maxDelayMs: 500, jitterMs: 25, maxConsecutiveFailures: 2)
expect(retryDelay(config, 4, 1000, 99)).to_equal(525)
val uploader = SerialBatchEventUploader.new(config)
uploader.enqueue(["a", "b", "c"])
uploader.failUntilDropped(2)
expect(uploader.droppedBatchCount()).to_equal(1)
expect(uploader.dropLog[0]).to_equal("2:2")
expect(joinText(uploader.pending)).to_equal("c")
```

</details>

#### should close by snapshotting pending count and resolving waiters

- Close with pending events and synthetic waiters
- uploader enqueue
- uploader flush
- uploader close
   - Expected: uploader.closed is true
   - Expected: uploader.pendingCount() equals `3`
   - Expected: uploader.pending.len() equals `0`
   - Expected: uploader.flushResolvers equals `0`
   - Expected: uploader.backpressureResolvers equals `0`
   - Expected: uploader.sleepResolve is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Close with pending events and synthetic waiters")
val uploader = SerialBatchEventUploader.new(SerialUploaderConfig.new(2, 10))
uploader.enqueue(["a", "b", "c"])
uploader.flush()
uploader.backpressureResolvers = 3
uploader.sleepResolve = true
uploader.close()
expect(uploader.closed).to_equal(true)
expect(uploader.pendingCount()).to_equal(3)
expect(uploader.pending.len()).to_equal(0)
expect(uploader.flushResolvers).to_equal(0)
expect(uploader.backpressureResolvers).to_equal(0)
expect(uploader.sleepResolve).to_equal(false)
```

</details>

#### should expose source-backed constants

- Pin modeled source surface
   - Expected: error.message equals `rate limited`
   - Expected: error.retryAfterMs equals `250`
   - Expected: serialUploaderSourceLinesModeled() equals `275`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin modeled source surface")
val error = RetryableError.new("rate limited", 250)
expect(error.message).to_equal("rate limited")
expect(error.retryAfterMs).to_equal(250)
expect(serialUploaderSourceLinesModeled()).to_equal(275)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
