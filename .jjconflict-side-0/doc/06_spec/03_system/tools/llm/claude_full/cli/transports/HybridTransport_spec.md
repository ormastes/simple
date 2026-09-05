# Claude Full Hybrid Transport

> Purpose: should convert websocket ingress URLs to post event URLs

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Hybrid Transport

Purpose: should convert websocket ingress URLs to post event URLs

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/transports/HybridTransport_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should convert websocket ingress URLs to post event URLs
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Hybrid Transport

Mirrors WebSocket-read plus HTTP-write hybrid transport behavior.

## Scenarios

### Claude full HybridTransport

#### should convert websocket ingress URLs to post event URLs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should convert websocket ingress URLs to post event URLs
- Verify: should convert websocket ingress URLs to post event URLs
- Convert a secure websocket URL
   - Expected: url equals `https://api.example.com/v2/session_ingress/session/session-1/events?x=1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should convert websocket ingress URLs to post event URLs")
step("Verify: should convert websocket ingress URLs to post event URLs")
# @req: REQ-TOOLS-Hybr-001
step("Convert a secure websocket URL")
val url = convertWsUrlToPostUrl("wss://api.example.com/v2/session_ingress/ws/session-1?x=1")
expect(url).to_equal("https://api.example.com/v2/session_ingress/session/session-1/events?x=1")
```

</details>

#### should delay stream events until flush

- should delay stream events until flush
- Verify: should delay stream events until flush
- Write two stream events
   - Expected: transport.pendingStreamCount() equals `2`
   - Expected: transport.streamEventTimerActive is true
   - Expected: transport.pendingStreamCount() equals `0`
   - Expected: transport.queuedBatchCount() equals `1`
   - Expected: transport.firstQueuedTypes() equals `stream_event,stream_event`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should delay stream events until flush")
step("Verify: should delay stream events until flush")
# @req: REQ-TOOLS-Hybr-001
step("Write two stream events")
val transport = hybridTransportNew("wss://api.example.com/v2/session_ingress/ws/s1", "token")
transport.write(hybridMessage("stream_event", "a"))
transport.write(hybridMessage("stream_event", "b"))
expect(transport.pendingStreamCount()).to_equal(2)  # oracle: value fixed by the spec contract
expect(transport.streamEventTimerActive).to_equal(true)
transport.flushStreamEvents()
expect(transport.pendingStreamCount()).to_equal(0)  # oracle: value fixed by the spec contract
expect(transport.queuedBatchCount()).to_equal(1)  # oracle: value fixed by the spec contract
expect(transport.firstQueuedTypes()).to_equal("stream_event,stream_event")
```

</details>

#### should flush buffered stream events before non-stream writes

- should flush buffered stream events before non-stream writes
- Verify: should flush buffered stream events before non-stream writes
- Write stream data followed by a result message
   - Expected: transport.postedBatchCount() equals `1`
   - Expected: transport.firstPostedTypes() equals `stream_event,result`
   - Expected: transport.streamEventTimerActive is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should flush buffered stream events before non-stream writes")
step("Verify: should flush buffered stream events before non-stream writes")
# @req: REQ-TOOLS-Hybr-001
step("Write stream data followed by a result message")
val transport = hybridTransportNew("ws://localhost/ws/s1", "token")
transport.write(hybridMessage("stream_event", "a"))
transport.write(hybridMessage("result", "done"))
expect(transport.postedBatchCount()).to_equal(1)  # oracle: value fixed by the spec contract
expect(transport.firstPostedTypes()).to_equal("stream_event,result")
expect(transport.streamEventTimerActive).to_equal(false)
```

</details>

#### should prepend buffered stream events to writeBatch

- should prepend buffered stream events to writeBatch
- Verify: should prepend buffered stream events to writeBatch
- Write stream data followed by an explicit batch
   - Expected: transport.firstPostedTypes() equals `stream_event,assistant,result`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should prepend buffered stream events to writeBatch")
step("Verify: should prepend buffered stream events to writeBatch")
# @req: REQ-TOOLS-Hybr-001
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

- should classify post statuses like retry policy
- Verify: should classify post statuses like retry policy
- Classify success, permanent, and retryable statuses
   - Expected: transport.postOnceStatus(204).diagnostic equals `success`
   - Expected: transport.postOnceStatus(400).permanent is true
   - Expected: transport.postOnceStatus(429).retryable is true
   - Expected: transport.postOnceStatus(503).retryable is true
   - Expected: transport.droppedBatchCount equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should classify post statuses like retry policy")
step("Verify: should classify post statuses like retry policy")
# @req: REQ-TOOLS-Hybr-001
step("Classify success, permanent, and retryable statuses")
val transport = HybridTransport.withFailureCap("wss://api/ws/s1", "token", 2)
expect(transport.postOnceStatus(204).diagnostic).to_equal("success")
expect(transport.postOnceStatus(400).permanent).to_equal(true)
expect(transport.postOnceStatus(429).retryable).to_equal(true)
expect(transport.postOnceStatus(503).retryable).to_equal(true)
expect(transport.droppedBatchCount).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### should return without retry when no session token is available

- should return without retry when no session token is available
- Verify: should return without retry when no session token is available
- Attempt a post without an ingress token
   - Expected: result.diagnostic equals `no-token`
   - Expected: result.retryable is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should return without retry when no session token is available")
step("Verify: should return without retry when no session token is available")
# @req: REQ-TOOLS-Hybr-001
step("Attempt a post without an ingress token")
val transport = hybridTransportNew("wss://api/ws/s1", "")
val result = transport.postOnceStatus(200)
expect(result.diagnostic).to_equal("no-token")
expect(result.retryable).to_equal(false)
```

</details>

#### should clear buffers and close inherited websocket state

- should clear buffers and close inherited websocket state
- Verify: should clear buffers and close inherited websocket state
- Close after buffering a stream event
   - Expected: transport.closed is true
   - Expected: transport.websocketClosed is true
   - Expected: transport.pendingStreamCount() equals `0`
   - Expected: hybridBatchFlushIntervalMs() equals `100`
   - Expected: hybridPostTimeoutMs() equals `15000`
   - Expected: hybridCloseGraceMs() equals `3000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should clear buffers and close inherited websocket state")
step("Verify: should clear buffers and close inherited websocket state")
# @req: REQ-TOOLS-Hybr-001
step("Close after buffering a stream event")
val transport = hybridTransportNew("wss://api/ws/s1", "token")
transport.write(hybridMessage("stream_event", "a"))
transport.close()
expect(transport.closed).to_equal(true)
expect(transport.websocketClosed).to_equal(true)
expect(transport.pendingStreamCount()).to_equal(0)  # oracle: value fixed by the spec contract
expect(hybridBatchFlushIntervalMs()).to_equal(100)  # oracle: value fixed by the spec contract
expect(hybridPostTimeoutMs()).to_equal(15000)  # oracle: value fixed by the spec contract
expect(hybridCloseGraceMs()).to_equal(3000)  # oracle: value fixed by the spec contract
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
- `REQ-TOOLS-Hybr-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a3a5d99ed1d309b61427138d40cb17c4ad7ed395e82c0a8fdc6aa4c72a8ca3ea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a3a5d99ed1d309b61427138d40cb17c4ad7ed395e82c0a8fdc6aa4c72a8ca3ea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a3a5d99ed1d309b61427138d40cb17c4ad7ed395e82c0a8fdc6aa4c72a8ca3ea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/cli/transports/HybridTransport_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/cli/transports/HybridTransport_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/cli/transports/HybridTransport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/cli/transports/HybridTransport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/cli/transports/HybridTransport_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should convert websocket ingress URLs to post event URLs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/HybridTransport_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should convert websocket ingress URLs to post event URLs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/transports/HybridTransport_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should delay stream events until flush' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/HybridTransport_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should delay stream events until flush' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/transports/HybridTransport_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should flush buffered stream events before non-stream writes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/HybridTransport_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should flush buffered stream events before non-stream writes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/transports/HybridTransport_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should prepend buffered stream events to writeBatch' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/HybridTransport_spec.spl:76:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify post statuses like retry policy' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/HybridTransport_spec.spl:89:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return without retry when no session token is available' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
