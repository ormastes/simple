# Claude Full Serial Batch Event Uploader

> Purpose: should enqueue and send batches serially

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Serial Batch Event Uploader

Purpose: should enqueue and send batches serially

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/transports/SerialBatchEventUploader_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should enqueue and send batches serially
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Serial Batch Event Uploader

Checks ordered batching, retry, backpressure, byte limits, and close accounting.

## Scenarios

### Claude full SerialBatchEventUploader

#### should enqueue and send batches serially

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should enqueue and send batches serially
- Verify: should enqueue and send batches serially
- Enqueue three events with max batch size two
   - Expected: uploader.sentBatches.len() equals `2`
   - Expected: uploader.firstSentBatchText() equals `a,b`
   - Expected: uploader.pendingCount() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should enqueue and send batches serially")
step("Verify: should enqueue and send batches serially")
# @req: REQ-TOOLS-Seri-001
step("Enqueue three events with max batch size two")
val uploader = SerialBatchEventUploader.new(SerialUploaderConfig.new(2, 10))
uploader.enqueue(["a", "b", "c"])
uploader.flushSuccess()
expect(uploader.sentBatches.len()).to_equal(2)  # oracle: value fixed by the spec contract
expect(uploader.firstSentBatchText()).to_equal("a,b")
expect(uploader.pendingCount()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### should apply backpressure when queue would exceed capacity

- should apply backpressure when queue would exceed capacity
- Verify: should apply backpressure when queue would exceed capacity
- Enqueue more events than the queue allows
   - Expected: uploader.pendingCount() equals `2`
   - Expected: uploader.backpressureResolvers equals `1`
   - Expected: uploader.backpressureResolvers equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should apply backpressure when queue would exceed capacity")
step("Verify: should apply backpressure when queue would exceed capacity")
# @req: REQ-TOOLS-Seri-001
step("Enqueue more events than the queue allows")
val uploader = SerialBatchEventUploader.new(SerialUploaderConfig.new(2, 2))
uploader.enqueue(["a", "b"])
uploader.enqueueOne("c")
expect(uploader.pendingCount()).to_equal(2)  # oracle: value fixed by the spec contract
expect(uploader.backpressureResolvers).to_equal(1)  # oracle: value fixed by the spec contract
uploader.flushSuccess()
expect(uploader.backpressureResolvers).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### should honor max batch bytes and drop unserializable items

- should honor max batch bytes and drop unserializable items
- Verify: should honor max batch bytes and drop unserializable items
- Take a byte-limited batch
   - Expected: joinText(batch) equals `abc`
   - Expected: joinText(uploader.pending) equals `de,fg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should honor max batch bytes and drop unserializable items")
step("Verify: should honor max batch bytes and drop unserializable items")
# @req: REQ-TOOLS-Seri-001
step("Take a byte-limited batch")
val uploader = serialUploaderWithByteLimit(5, 7, 10)
uploader.enqueue(["abc", "de", "UNSERIALIZABLE", "fg"])
val batch = uploader.takeBatch()
expect(joinText(batch)).to_equal("abc")
expect(joinText(uploader.pending)).to_equal("de,fg")
```

</details>

#### should requeue failed batches and compute retry delay

- should requeue failed batches and compute retry delay
- Verify: should requeue failed batches and compute retry delay
- Fail the first batch and observe front requeue
   - Expected: delay equals `110`
   - Expected: joinText(uploader.pending) equals `a,b,c`
   - Expected: uploader.sleepResolve is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should requeue failed batches and compute retry delay")
step("Verify: should requeue failed batches and compute retry delay")
# @req: REQ-TOOLS-Seri-001
step("Fail the first batch and observe front requeue")
val config = serialUploaderConfig(2, 10, 100, 500, 50)
val uploader = SerialBatchEventUploader.new(config)
uploader.enqueue(["a", "b", "c"])
val delay = uploader.failOnce(0, 10)
expect(delay).to_equal(110)  # oracle: value fixed by the spec contract
expect(joinText(uploader.pending)).to_equal("a,b,c")
expect(uploader.sleepResolve).to_equal(true)
```

</details>

#### should clamp retry-after delays and drop after failure cap

- should clamp retry-after delays and drop after failure cap
- Verify: should clamp retry-after delays and drop after failure cap
- Use server retry-after and then hit the drop cap
   - Expected: retryDelay(config, 4, 1000, 99) equals `525`
   - Expected: uploader.droppedBatchCount() equals `1`
   - Expected: uploader.dropLog[0] equals `2:2`
   - Expected: joinText(uploader.pending) equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should clamp retry-after delays and drop after failure cap")
step("Verify: should clamp retry-after delays and drop after failure cap")
# @req: REQ-TOOLS-Seri-001
step("Use server retry-after and then hit the drop cap")
val config = SerialUploaderConfig(maxBatchSize: 2, maxBatchBytes: 0, maxQueueSize: 10, baseDelayMs: 100, maxDelayMs: 500, jitterMs: 25, maxConsecutiveFailures: 2)
expect(retryDelay(config, 4, 1000, 99)).to_equal(525)  # oracle: value fixed by the spec contract
val uploader = SerialBatchEventUploader.new(config)
uploader.enqueue(["a", "b", "c"])
uploader.failUntilDropped(2)
expect(uploader.droppedBatchCount()).to_equal(1)  # oracle: value fixed by the spec contract
expect(uploader.dropLog[0]).to_equal("2:2")
expect(joinText(uploader.pending)).to_equal("c")
```

</details>

#### should close by snapshotting pending count and resolving waiters

- should close by snapshotting pending count and resolving waiters
- Verify: should close by snapshotting pending count and resolving waiters
- Close with pending events and synthetic waiters
   - Expected: uploader.closed is true
   - Expected: uploader.pendingCount() equals `3`
   - Expected: uploader.pending.len() equals `0`
   - Expected: uploader.flushResolvers equals `0`
   - Expected: uploader.backpressureResolvers equals `0`
   - Expected: uploader.sleepResolve is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should close by snapshotting pending count and resolving waiters")
step("Verify: should close by snapshotting pending count and resolving waiters")
# @req: REQ-TOOLS-Seri-001
step("Close with pending events and synthetic waiters")
val uploader = SerialBatchEventUploader.new(SerialUploaderConfig.new(2, 10))
uploader.enqueue(["a", "b", "c"])
uploader.flush()
uploader.backpressureResolvers = 3
uploader.sleepResolve = true
uploader.close()
expect(uploader.closed).to_equal(true)
expect(uploader.pendingCount()).to_equal(3)  # oracle: value fixed by the spec contract
expect(uploader.pending.len()).to_equal(0)  # oracle: value fixed by the spec contract
expect(uploader.flushResolvers).to_equal(0)  # oracle: value fixed by the spec contract
expect(uploader.backpressureResolvers).to_equal(0)  # oracle: value fixed by the spec contract
expect(uploader.sleepResolve).to_equal(false)
```

</details>

#### should expose source-backed constants

- should expose source-backed constants
- Verify: should expose source-backed constants
- Pin modeled source surface
   - Expected: error.message equals `rate limited`
   - Expected: error.retryAfterMs equals `250`
   - Expected: serialUploaderSourceLinesModeled() equals `275`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose source-backed constants")
step("Verify: should expose source-backed constants")
# @req: REQ-TOOLS-Seri-001
step("Pin modeled source surface")
val error = RetryableError.new("rate limited", 250)
expect(error.message).to_equal("rate limited")
expect(error.retryAfterMs).to_equal(250)  # oracle: value fixed by the spec contract
expect(serialUploaderSourceLinesModeled()).to_equal(275)  # oracle: value fixed by the spec contract
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Seri-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `25ff13d3f6777d1af19901b77b0eef503f445fd728dec40b1b59daa02ac543f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `25ff13d3f6777d1af19901b77b0eef503f445fd728dec40b1b59daa02ac543f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `25ff13d3f6777d1af19901b77b0eef503f445fd728dec40b1b59daa02ac543f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/cli/transports/SerialBatchEventUploader_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/cli/transports/SerialBatchEventUploader_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/cli/transports/SerialBatchEventUploader_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/cli/transports/SerialBatchEventUploader_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/cli/transports/SerialBatchEventUploader_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should enqueue and send batches serially' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/SerialBatchEventUploader_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should enqueue and send batches serially' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/transports/SerialBatchEventUploader_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should apply backpressure when queue would exceed capacity' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/SerialBatchEventUploader_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should apply backpressure when queue would exceed capacity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/transports/SerialBatchEventUploader_spec.spl:51:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should honor max batch bytes and drop unserializable items' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/SerialBatchEventUploader_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should honor max batch bytes and drop unserializable items' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/transports/SerialBatchEventUploader_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should requeue failed batches and compute retry delay' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/SerialBatchEventUploader_spec.spl:77:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should clamp retry-after delays and drop after failure cap' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/SerialBatchEventUploader_spec.spl:92:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should close by snapshotting pending count and resolving waiters' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
