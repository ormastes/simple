# Claude Full Bridge REPL Transport

> Checks v1/v2 transport adapter state without opening network transports.

<!-- sdn-diagram:id=replBridgeTransport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=replBridgeTransport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

replBridgeTransport_spec -> std
replBridgeTransport_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=replBridgeTransport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge REPL Transport

Checks v1/v2 transport adapter state without opening network transports.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/bridge/replBridgeTransport_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks v1/v2 transport adapter state without opening network transports.

## Scenarios

### Claude full bridge repl transport

#### adapts v1 hybrid transport semantics

- v1 carries no SSE sequence number and report methods are no-ops
   - Expected: transport.getLastSequenceNum() equals `v1LastSequenceNum()`
   - Expected: transport.droppedBatchCount equals `3`
   - Expected: transport.isConnectedStatus() is false
- transport connect
   - Expected: transport.isConnectedStatus() is true
- transport write
- transport writeBatch
- transport reportState
- transport flush
   - Expected: transport.writes equals `["one", "two", "three"]`
   - Expected: transport.stateReports.len() equals `0`
   - Expected: transport.flushed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("v1 carries no SSE sequence number and report methods are no-ops")
val transport = createV1ReplTransport(99, 3)
expect(transport.getLastSequenceNum()).to_equal(v1LastSequenceNum())
expect(transport.droppedBatchCount).to_equal(3)
expect(transport.isConnectedStatus()).to_equal(false)
transport.connect()
expect(transport.isConnectedStatus()).to_equal(true)
transport.write("one")
transport.writeBatch(["two", "three"])
transport.reportState("requires_action")
transport.flush()
expect(transport.writes).to_equal(["one", "two", "three"])
expect(transport.stateReports.len()).to_equal(0)
expect(transport.flushed).to_equal(false)
```

</details>

#### builds v2 transport with registered epoch and sequence carryover

- v2 uses SSE reads, CCRClient writes, and preserves sequence high-water mark
   - Expected: transport.epoch equals `42`
   - Expected: transport.getLastSequenceNum() equals `7`
   - Expected: transport.droppedBatchCount equals `v2DroppedBatchCount()`
   - Expected: transport.getStateLabel() equals `connecting`
- transport connect
   - Expected: transport.isConnectedStatus() is true
   - Expected: transport.getStateLabel() equals `connected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("v2 uses SSE reads, CCRClient writes, and preserves sequence high-water mark")
val opts = ReplTransportOpts.new("https://api/v1/code/sessions/cse_1", "jwt", "cse_1").withInitialSequenceNum(7)
val transport = createV2ReplTransport(opts, 42)
expect(transport.epoch).to_equal(42)
expect(transport.getLastSequenceNum()).to_equal(7)
expect(transport.droppedBatchCount).to_equal(v2DroppedBatchCount())
expect(transport.getStateLabel()).to_equal("connecting")
transport.connect()
expect(transport.isConnectedStatus()).to_equal(true)
expect(transport.getStateLabel()).to_equal("connected")
expect(transport.logs[0]).to_contain("via registerWorker")
```

</details>

#### uses provided bridge epoch without registering

- /bridge response epoch wins over registerWorker
   - Expected: shouldRegisterWorker(opts) is false
   - Expected: resolvedEpoch(opts, 42) equals `99`
   - Expected: transport.epoch equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("/bridge response epoch wins over registerWorker")
val opts = ReplTransportOpts.new("https://api/v1/code/sessions/cse_1", "jwt", "cse_1").withEpoch(99)
expect(shouldRegisterWorker(opts)).to_equal(false)
expect(resolvedEpoch(opts, 42)).to_equal(99)
val transport = createV2ReplTransport(opts, 42)
expect(transport.epoch).to_equal(99)
expect(transport.logs[0]).to_contain("from /bridge")
```

</details>

#### supports outbound-only v2 write path

- Outbound-only skips SSE read open but initializes writes
- transport connect
   - Expected: transport.outboundOnly is true
   - Expected: transport.connected is false
   - Expected: transport.isConnectedStatus() is true
- transport writeBatch
   - Expected: transport.writes equals `["a", "b"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Outbound-only skips SSE read open but initializes writes")
val opts = ReplTransportOpts.new("https://api/v1/code/sessions/cse_1", "jwt", "cse_1").outbound()
val transport = createV2ReplTransport(opts, 42)
transport.connect()
expect(transport.outboundOnly).to_equal(true)
expect(transport.connected).to_equal(false)
expect(transport.isConnectedStatus()).to_equal(true)
transport.writeBatch(["a", "b"])
expect(transport.writes).to_equal(["a", "b"])
```

</details>

#### records v2 state, metadata, delivery, and flush calls

- CCRClient owns writes, worker state, metadata, delivery, and flush
- transport reportState
- transport reportMetadata
- transport reportDelivery
- transport receiveEvent
- transport flush
   - Expected: transport.stateReports equals `["requires_action"]`
   - Expected: transport.metadataReports equals `["title=Hi"]`
   - Expected: transport.deliveries equals `["evt_1:processing", "evt_2:received", "evt_2:processed"]`
   - Expected: transport.flushed is true
   - Expected: transport.getLastSequenceNum() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("CCRClient owns writes, worker state, metadata, delivery, and flush")
val transport = createV2ReplTransport(ReplTransportOpts.new("https://api/v1/code/sessions/cse_1", "jwt", "cse_1"), 42)
transport.reportState("requires_action")
transport.reportMetadata("title=Hi")
transport.reportDelivery("evt_1", "processing")
transport.receiveEvent("evt_2", "payload")
transport.flush()
expect(transport.stateReports).to_equal(["requires_action"])
expect(transport.metadataReports).to_equal(["title=Hi"])
expect(transport.deliveries).to_equal(["evt_1:processing", "evt_2:received", "evt_2:processed"])
expect(transport.flushed).to_equal(true)
expect(transport.getLastSequenceNum()).to_equal(1)
```

</details>

#### maps v2 close and failure paths to synthetic close codes

- Epoch mismatch, init failure, and SSE exhaustion are distinguishable
- transport epochMismatch
   - Expected: transport.closed is true
   - Expected: transport.closeCodes[0] equals `epochMismatchCloseCode()`
- failed initFailure
   - Expected: failed.closeCodes[0] equals `initFailureCloseCode()`
- exhausted sseClose
   - Expected: exhausted.closeCodes[0] equals `sseExhaustedCloseCode()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Epoch mismatch, init failure, and SSE exhaustion are distinguishable")
val transport = createV2ReplTransport(ReplTransportOpts.new("https://api/v1/code/sessions/cse_1", "jwt", "cse_1"), 42)
transport.epochMismatch()
expect(transport.closed).to_equal(true)
expect(transport.closeCodes[0]).to_equal(epochMismatchCloseCode())
val failed = createV2ReplTransport(ReplTransportOpts.new("https://api/v1/code/sessions/cse_1", "jwt", "cse_1"), 42)
failed.initFailure("down")
expect(failed.closeCodes[0]).to_equal(initFailureCloseCode())
val exhausted = createV2ReplTransport(ReplTransportOpts.new("https://api/v1/code/sessions/cse_1", "jwt", "cse_1"), 42)
exhausted.sseClose(0)
expect(exhausted.closeCodes[0]).to_equal(sseExhaustedCloseCode())
```

</details>

#### exports construction and auth helpers

- Keep URL, auth, and option decisions source-backed
   - Expected: deriveSseStreamUrl("https://api/v1/code/sessions/cse_1/") equals `https://api/v1/code/sessions/cse_1/worker/events/stream`
   - Expected: getAuthHeader("jwt") equals `Authorization: Bearer jwt`
   - Expected: getAuthHeader("") equals ``
   - Expected: shouldUsePerInstanceAuth(opts) is true
   - Expected: shouldUpdateProcessWideAuth(opts) is false
   - Expected: defaultHeartbeatIntervalMs() equals `20000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep URL, auth, and option decisions source-backed")
val opts = ReplTransportOpts.new("https://api/v1/code/sessions/cse_1", "jwt", "cse_1").perInstanceAuth()
expect(deriveSseStreamUrl("https://api/v1/code/sessions/cse_1/")).to_equal("https://api/v1/code/sessions/cse_1/worker/events/stream")
expect(getAuthHeader("jwt")).to_equal("Authorization: Bearer jwt")
expect(getAuthHeader("")).to_equal("")
expect(shouldUsePerInstanceAuth(opts)).to_equal(true)
expect(shouldUpdateProcessWideAuth(opts)).to_equal(false)
expect(defaultHeartbeatIntervalMs()).to_equal(20000)
```

</details>

#### exports adapter constants

- Names document the v1/v2 split and recovery behavior
   - Expected: v1ReadTransportName() equals `HybridTransport`
   - Expected: v2ReadTransportName() equals `SSETransport`
   - Expected: v2WriteTransportName() equals `CCRClient`
   - Expected: v2WritePathName() equals `CCRClient.writeEvent`
   - Expected: sseWritePathIsUsedForV2() is false
   - Expected: v2DeliveryStatusesOnReceive() equals `["received", "processed"]`
   - Expected: v2CloseRecoveryOwner() equals `poll loop`
   - Expected: closeCodeMeaning(4090) equals `epoch mismatch`
   - Expected: v1WritePathName() equals `HybridTransport.write`
   - Expected: v2InitializeMethodName() equals `CCRClient.initialize`
   - Expected: v2HeartbeatOwner() equals `CCRClient`
   - Expected: v2ReceivedDeliveryAutoFired() is true
   - Expected: v2ProcessedDeliveryImmediateAck() is true
   - Expected: v2OnCloseSseUndefinedMapsTo4092() is true
   - Expected: v2SessionUrlToSsePathSuffix() equals `/worker/events/stream`
   - Expected: v2WorkerDeliveryStatusProcessed() equals `processed`
   - Expected: transportUsesSingleAdapterInterface() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Names document the v1/v2 split and recovery behavior")
expect(v1ReadTransportName()).to_equal("HybridTransport")
expect(v2ReadTransportName()).to_equal("SSETransport")
expect(v2WriteTransportName()).to_equal("CCRClient")
expect(v2WritePathName()).to_equal("CCRClient.writeEvent")
expect(sseWritePathIsUsedForV2()).to_equal(false)
expect(v2DeliveryStatusesOnReceive()).to_equal(["received", "processed"])
expect(v2CloseRecoveryOwner()).to_equal("poll loop")
expect(reportStateEndpointPurpose()).to_contain("/worker state")
expect(reportMetadataEndpointPurpose()).to_contain("external_metadata")
expect(reportDeliveryEndpointPurpose()).to_contain("/delivery")
expect(flushPurpose()).to_contain("write queue")
expect(sequenceCarryoverPurpose()).to_contain("old stream")
expect(outboundOnlyPurpose()).to_contain("skip opening")
expect(closeCodeMeaning(4090)).to_equal("epoch mismatch")
expect(v1WritePathName()).to_equal("HybridTransport.write")
expect(v2InitializeMethodName()).to_equal("CCRClient.initialize")
expect(v2HeartbeatOwner()).to_equal("CCRClient")
expect(v2ReceivedDeliveryAutoFired()).to_equal(true)
expect(v2ProcessedDeliveryImmediateAck()).to_equal(true)
expect(v2OnCloseSseUndefinedMapsTo4092()).to_equal(true)
expect(v2SessionUrlToSsePathSuffix()).to_equal("/worker/events/stream")
expect(v2WorkerDeliveryStatusProcessed()).to_equal("processed")
expect(transportUsesSingleAdapterInterface()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
