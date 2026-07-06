# Claude Full Worker State Uploader

> Checks coalescing, retry delay, bounded pending state, and close behavior.

<!-- sdn-diagram:id=WorkerStateUploader_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=WorkerStateUploader_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

WorkerStateUploader_spec -> std
WorkerStateUploader_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=WorkerStateUploader_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Worker State Uploader

Checks coalescing, retry delay, bounded pending state, and close behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/transports/WorkerStateUploader_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks coalescing, retry delay, bounded pending state, and close behavior.

## Scenarios

### Claude full WorkerStateUploader

#### coalesces top-level and metadata patches

- Top-level overlay wins while metadata merges by key
   - Expected: merged.worker_status equals `done`
   - Expected: merged.external_metadata equals `["a=1", "b=3", "c=null"]`
   - Expected: merged.internal_metadata equals `["x=1", "y=2"]`
   - Expected: merged.other equals `old`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Top-level overlay wins while metadata merges by key")
val base = WorkerPatch(worker_status: "running", external_metadata: ["a=1", "b=2"], internal_metadata: ["x=1"], other: "old")
val overlay = WorkerPatch(worker_status: "done", external_metadata: ["b=3", "c=null"], internal_metadata: ["y=2"], other: "")
val merged = coalescePatches(base, overlay)
expect(merged.worker_status).to_equal("done")
expect(merged.external_metadata).to_equal(["a=1", "b=3", "c=null"])
expect(merged.internal_metadata).to_equal(["x=1", "y=2"])
expect(merged.other).to_equal("old")
```

</details>

#### enqueues and closes without growing pending slots

- Pending coalesces, close clears it
- uploader enqueue
- uploader enqueue
   - Expected: pending.worker_status equals `two`
   - Expected: pending.external_metadata equals `["a=1"]`
   - Expected: "missing pending" equals `pending`
- uploader close
   - Expected: uploader.closed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pending coalesces, close clears it")
val uploader = WorkerStateUploader.new(WorkerStateUploaderConfig.new(100, 1000, 10))
uploader.inflight = true
uploader.enqueue(WorkerPatch(worker_status: "one", external_metadata: [], internal_metadata: [], other: ""))
uploader.enqueue(WorkerPatch(worker_status: "two", external_metadata: ["a=1"], internal_metadata: [], other: ""))
if val Some(pending) = uploader.pending:
    expect(pending.worker_status).to_equal("two")
    expect(pending.external_metadata).to_equal(["a=1"])
else:
    expect("missing pending").to_equal("pending")
uploader.close()
expect(uploader.closed).to_equal(true)
expect(uploader.pending).to_be_nil()
```

</details>

#### drains successful sends and absorbs pending before retry

- Success sends payload; retry coalesces pending into current
- uploader enqueue
   - Expected: uploader.sent.len() equals `1`
- uploader pending = Some
   - Expected: current.worker_status equals `done`
   - Expected: current.external_metadata equals `["a=2"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Success sends payload; retry coalesces pending into current")
val uploader = WorkerStateUploader.new(WorkerStateUploaderConfig.new(100, 1000, 10))
uploader.enqueue(WorkerPatch(worker_status: "running", external_metadata: [], internal_metadata: [], other: ""))
expect(uploader.sent.len()).to_equal(1)
uploader.pending = Some(WorkerPatch(worker_status: "done", external_metadata: ["a=2"], internal_metadata: [], other: ""))
val current = uploader.absorbPendingForRetry(WorkerPatch(worker_status: "running", external_metadata: ["a=1"], internal_metadata: [], other: ""))
expect(current.worker_status).to_equal("done")
expect(current.external_metadata).to_equal(["a=2"])
expect(uploader.pending).to_be_nil()
```

</details>

#### computes exponential retry delay

- Delay doubles, clamps, and adds bounded jitter
   - Expected: retryDelay(config, 1, 10) equals `110`
   - Expected: retryDelay(config, 3, 10) equals `410`
   - Expected: retryDelay(config, 5, 99) equals `550`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Delay doubles, clamps, and adds bounded jitter")
val config = WorkerStateUploaderConfig.new(100, 500, 50)
expect(retryDelay(config, 1, 10)).to_equal(110)
expect(retryDelay(config, 3, 10)).to_equal(410)
expect(retryDelay(config, 5, 99)).to_equal(550)
```

</details>

#### exports source-backed constants

- Pin uploader contract
   - Expected: mergeMetadata(["a=1"], ["a=null"]) equals `["a=null"]`
   - Expected: metadataKey("abc=def") equals `abc`
   - Expected: boundedPendingSlots() equals `2`
   - Expected: topLevelLastValueWins() is true
   - Expected: metadataUsesRfc7396Merge() is true
   - Expected: nullMetadataValuesPreservedForServerDelete() is true
   - Expected: retriesUntilSuccessOrClose() is true
   - Expected: fireAndForgetEnqueue() is true
   - Expected: noBackpressureNeeded() is true
   - Expected: putWorkerPath() equals `/worker`
   - Expected: workerStateUploaderSourceLinesModeled() equals `98`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin uploader contract")
expect(mergeMetadata(["a=1"], ["a=null"])).to_equal(["a=null"])
expect(metadataKey("abc=def")).to_equal("abc")
expect(boundedPendingSlots()).to_equal(2)
expect(topLevelLastValueWins()).to_equal(true)
expect(metadataUsesRfc7396Merge()).to_equal(true)
expect(nullMetadataValuesPreservedForServerDelete()).to_equal(true)
expect(retriesUntilSuccessOrClose()).to_equal(true)
expect(fireAndForgetEnqueue()).to_equal(true)
expect(noBackpressureNeeded()).to_equal(true)
expect(putWorkerPath()).to_equal("/worker")
expect(workerStateUploaderSourceLinesModeled()).to_equal(98)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
