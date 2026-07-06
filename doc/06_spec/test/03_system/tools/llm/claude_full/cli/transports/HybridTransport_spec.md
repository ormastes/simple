# Claude Full Hybrid Transport

> Mirrors WebSocket-read plus HTTP-write hybrid transport behavior.

<!-- sdn-diagram:id=HybridTransport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=HybridTransport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

HybridTransport_spec -> std
HybridTransport_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=HybridTransport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Hybrid Transport

Mirrors WebSocket-read plus HTTP-write hybrid transport behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/transports/HybridTransport_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors WebSocket-read plus HTTP-write hybrid transport behavior.

## Scenarios

### Claude full HybridTransport

#### should convert websocket ingress URLs to post event URLs

- Convert a secure websocket URL
   - Expected: url equals `https://api.example.com/v2/session_ingress/session/session-1/events?x=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Convert a secure websocket URL")
val url = convertWsUrlToPostUrl("wss://api.example.com/v2/session_ingress/ws/session-1?x=1")
expect(url).to_equal("https://api.example.com/v2/session_ingress/session/session-1/events?x=1")
```

</details>

#### should delay stream events until flush

- Write two stream events
- transport write
- transport write
   - Expected: transport.pendingStreamCount() equals `2`
   - Expected: transport.streamEventTimerActive is true
- transport flushStreamEvents
   - Expected: transport.pendingStreamCount() equals `0`
   - Expected: transport.queuedBatchCount() equals `1`
   - Expected: transport.firstQueuedTypes() equals `stream_event,stream_event`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write two stream events")
val transport = hybridTransportNew("wss://api.example.com/v2/session_ingress/ws/s1", "token")
transport.write(hybridMessage("stream_event", "a"))
transport.write(hybridMessage("stream_event", "b"))
expect(transport.pendingStreamCount()).to_equal(2)
expect(transport.streamEventTimerActive).to_equal(true)
transport.flushStreamEvents()
expect(transport.pendingStreamCount()).to_equal(0)
expect(transport.queuedBatchCount()).to_equal(1)
expect(transport.firstQueuedTypes()).to_equal("stream_event,stream_event")
```

</details>

#### should flush buffered stream events before non-stream writes

- Write stream data followed by a result message
- transport write
- transport write
   - Expected: transport.postedBatchCount() equals `1`
   - Expected: transport.firstPostedTypes() equals `stream_event,result`
   - Expected: transport.streamEventTimerActive is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write stream data followed by a result message")
val transport = hybridTransportNew("ws://localhost/ws/s1", "token")
transport.write(hybridMessage("stream_event", "a"))
transport.write(hybridMessage("result", "done"))
expect(transport.postedBatchCount()).to_equal(1)
expect(transport.firstPostedTypes()).to_equal("stream_event,result")
expect(transport.streamEventTimerActive).to_equal(false)
```

</details>

#### should prepend buffered stream events to writeBatch

- Write stream data followed by an explicit batch
- batch push
- batch push
- transport write
- transport writeBatch
   - Expected: transport.firstPostedTypes() equals `stream_event,assistant,result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Write stream data followed by an explicit batch")
val transport = hybridTransportNew("ws://localhost/ws/s1", "token")
var batch: [HybridMessage] = []
batch.push(hybridMessage("assistant", "m1"))
batch.push(hybridMessage("result", "ok"))
transport.write(hybridMessage("stream_event", "a"))
transport.writeBatch(batch)
expect(transport.firstPostedTypes()).to_equal("stream_event,assistant,result")
```

</details>

#### should classify post statuses like retry policy

- Classify success, permanent, and retryable statuses
   - Expected: transport.postOnceStatus(204).diagnostic equals `success`
   - Expected: transport.postOnceStatus(400).permanent is true
   - Expected: transport.postOnceStatus(429).retryable is true
   - Expected: transport.postOnceStatus(503).retryable is true
   - Expected: transport.droppedBatchCount equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Classify success, permanent, and retryable statuses")
val transport = HybridTransport.withFailureCap("wss://api/ws/s1", "token", 2)
expect(transport.postOnceStatus(204).diagnostic).to_equal("success")
expect(transport.postOnceStatus(400).permanent).to_equal(true)
expect(transport.postOnceStatus(429).retryable).to_equal(true)
expect(transport.postOnceStatus(503).retryable).to_equal(true)
expect(transport.droppedBatchCount).to_equal(1)
```

</details>

#### should return without retry when no session token is available

- Attempt a post without an ingress token
   - Expected: result.diagnostic equals `no-token`
   - Expected: result.retryable is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Attempt a post without an ingress token")
val transport = hybridTransportNew("wss://api/ws/s1", "")
val result = transport.postOnceStatus(200)
expect(result.diagnostic).to_equal("no-token")
expect(result.retryable).to_equal(false)
```

</details>

#### should clear buffers and close inherited websocket state

- Close after buffering a stream event
- transport write
- transport close
   - Expected: transport.closed is true
   - Expected: transport.websocketClosed is true
   - Expected: transport.pendingStreamCount() equals `0`
   - Expected: hybridBatchFlushIntervalMs() equals `100`
   - Expected: hybridPostTimeoutMs() equals `15000`
   - Expected: hybridCloseGraceMs() equals `3000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Close after buffering a stream event")
val transport = hybridTransportNew("wss://api/ws/s1", "token")
transport.write(hybridMessage("stream_event", "a"))
transport.close()
expect(transport.closed).to_equal(true)
expect(transport.websocketClosed).to_equal(true)
expect(transport.pendingStreamCount()).to_equal(0)
expect(hybridBatchFlushIntervalMs()).to_equal(100)
expect(hybridPostTimeoutMs()).to_equal(15000)
expect(hybridCloseGraceMs()).to_equal(3000)
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
