# Claude Full Worker State Uploader

> Checks coalescing, retry delay, bounded pending state, and close behavior.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks coalescing, retry delay, bounded pending state, and close behavior.

## Scenarios

### Claude full WorkerStateUploader

#### coalesces top-level and metadata patches

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- coalesces top-level and metadata patches
- Top-level overlay wins while metadata merges by key
   - Expected: merged.worker_status equals `done`
   - Expected: merged.external_metadata equals `["a=1", "b=3", "c=null"]`
   - Expected: merged.internal_metadata equals `["x=1", "y=2"]`
   - Expected: merged.other equals `old`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("coalesces top-level and metadata patches")
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

- enqueues and closes without growing pending slots
- Pending coalesces, close clears it
   - Expected: pending.worker_status equals `two`
   - Expected: pending.external_metadata equals `["a=1"]`
   - Expected: "missing pending" equals `pending`
   - Expected: uploader.closed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enqueues and closes without growing pending slots")
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

- drains successful sends and absorbs pending before retry
- Success sends payload; retry coalesces pending into current
   - Expected: uploader.sent.len() equals `1`
   - Expected: current.worker_status equals `done`
   - Expected: current.external_metadata equals `["a=2"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("drains successful sends and absorbs pending before retry")
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

- computes exponential retry delay
- Delay doubles, clamps, and adds bounded jitter
   - Expected: retryDelay(config, 1, 10) equals `110`
   - Expected: retryDelay(config, 3, 10) equals `410`
   - Expected: retryDelay(config, 5, 99) equals `550`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes exponential retry delay")
step("Delay doubles, clamps, and adds bounded jitter")
val config = WorkerStateUploaderConfig.new(100, 500, 50)
expect(retryDelay(config, 1, 10)).to_equal(110)
expect(retryDelay(config, 3, 10)).to_equal(410)
expect(retryDelay(config, 5, 99)).to_equal(550)
```

</details>

#### exports source-backed constants

- exports source-backed constants
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

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exports source-backed constants")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `da3c041ea56ae6b6cd78acd672cb79fae32cc8220eaabb39169babea5fbebde2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `da3c041ea56ae6b6cd78acd672cb79fae32cc8220eaabb39169babea5fbebde2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `da3c041ea56ae6b6cd78acd672cb79fae32cc8220eaabb39169babea5fbebde2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/cli/transports/WorkerStateUploader_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/cli/transports/WorkerStateUploader_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/cli/transports/WorkerStateUploader_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/cli/transports/WorkerStateUploader_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/cli/transports/WorkerStateUploader_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/cli/transports/WorkerStateUploader_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'coalesces top-level and metadata patches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/transports/WorkerStateUploader_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enqueues and closes without growing pending slots' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/transports/WorkerStateUploader_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'drains successful sends and absorbs pending before retry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
