# Claude Full SSE Transport

> Purpose: should parse complete frames and keep incomplete remainder

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full SSE Transport

Purpose: should parse complete frames and keep incomplete remainder

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/transports/SSETransport_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should parse complete frames and keep incomplete remainder
Audience: compiler and tooling engineers who maintain this spec

# Claude Full SSE Transport

Checks SSE frame parsing, sequence resume state, reconnects, writes, and close.

## Scenarios

### Claude full SSETransport

#### should parse complete frames and keep incomplete remainder

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should parse complete frames and keep incomplete remainder
- Verify: should parse complete frames and keep incomplete remainder
- Parse comment, multi-data, and partial SSE input
   - Expected: parsed.frames.len() equals `2`
   - Expected: parsed.frames[0].comment is true
   - Expected: parsed.frames[1].id equals `7`
   - Expected: parsed.frames[1].data equals `7|assistant|hello\nworld`
   - Expected: parsed.remaining equals `id: `


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should parse complete frames and keep incomplete remainder")
step("Verify: should parse complete frames and keep incomplete remainder")
# @req: REQ-TOOLS-Sset-001
step("Parse comment, multi-data, and partial SSE input")
val parsed = parseSSEFrames(":keepalive\n\nid: 7\nevent: client_event\ndata: 7|assistant|hello\ndata: world\n\nid: ")
expect(parsed.frames.len()).to_equal(2)  # oracle: value fixed by the spec contract
expect(parsed.frames[0].comment).to_equal(true)
expect(parsed.frames[1].id).to_equal("7")
expect(parsed.frames[1].data).to_equal("7|assistant|hello\nworld")
expect(parsed.remaining).to_equal("id: ")
```

</details>

#### should connect, read client events, and update sequence high-water mark

- should connect, read client events, and update sequence high-water mark
- Verify: should connect, read client events, and update sequence high-water mark
- Connect and process one client_event frame
   - Expected: transport.isConnectedStatus() is true
   - Expected: transport.getLastSequenceNum() equals `5`
   - Expected: transport.dataLines[0] equals `payload\n`
   - Expected: transport.eventLog[0].payload_type equals `assistant`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should connect, read client events, and update sequence high-water mark")
step("Verify: should connect, read client events, and update sequence high-water mark")
# @req: REQ-TOOLS-Sset-001
step("Connect and process one client_event frame")
val transport = SSETransport.new("https://api/session/s1/events/stream", "s1", 3)
transport.connect(200, true)
transport.readText("id: 5\nevent: client_event\ndata: 5|assistant|payload\n\n")
expect(transport.isConnectedStatus()).to_equal(true)
expect(transport.getLastSequenceNum()).to_equal(5)  # oracle: value fixed by the spec contract
expect(transport.dataLines[0]).to_equal("payload\n")
expect(transport.eventLog[0].payload_type).to_equal("assistant")
```

</details>

#### should diagnose duplicate, unexpected, and missing-event frames

- should diagnose duplicate, unexpected, and missing-event frames
- Verify: should diagnose duplicate, unexpected, and missing-event frames
- Read frames that should not be delivered as payload
   - Expected: transport.getLastSequenceNum() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should diagnose duplicate, unexpected, and missing-event frames")
step("Verify: should diagnose duplicate, unexpected, and missing-event frames")
# @req: REQ-TOOLS-Sset-001
step("Read frames that should not be delivered as payload")
val transport = SSETransport.new("https://api/session/s1/events/stream", "", 0)
transport.connect(200, true)
transport.readText("id: 4\nevent: other\ndata: x\n\nid: 4\ndata: y\n\n")
expect(transport.getLastSequenceNum()).to_equal(4)  # oracle: value fixed by the spec contract
expect(transport.diagnostics).to_contain("cli_sse_unexpected_event_type")
expect(transport.diagnostics).to_contain("cli_sse_duplicate_sequence")
expect(transport.diagnostics).to_contain("cli_sse_frame_missing_event_field")
```

</details>

#### should close permanently on permanent connect HTTP status

- should close permanently on permanent connect HTTP status
- Verify: should close permanently on permanent connect HTTP status
- Connect with unauthorized response
   - Expected: transport.isClosedStatus() is true
   - Expected: transport.closeCodes[0] equals `401`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should close permanently on permanent connect HTTP status")
step("Verify: should close permanently on permanent connect HTTP status")
# @req: REQ-TOOLS-Sset-001
step("Connect with unauthorized response")
val transport = SSETransport.new("https://api/session/s1/events/stream", "", 0)
transport.connect(401, true)
expect(transport.isClosedStatus()).to_equal(true)
expect(transport.closeCodes[0]).to_equal(401)  # oracle: value fixed by the spec contract
```

</details>

#### should schedule reconnects and exhaust the reconnect budget

- should schedule reconnects and exhaust the reconnect budget
- Verify: should schedule reconnects and exhaust the reconnect budget
- Handle transient errors then budget exhaustion
   - Expected: transport.state equals `reconnecting`
   - Expected: transport.reconnectAttempts equals `1`
   - Expected: transport.reconnectTimerActive is true
   - Expected: transport.isClosedStatus() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should schedule reconnects and exhaust the reconnect budget")
step("Verify: should schedule reconnects and exhaust the reconnect budget")
# @req: REQ-TOOLS-Sset-001
step("Handle transient errors then budget exhaustion")
val transport = SSETransport.new("https://api/session/s1/events/stream", "", 0)
transport.connect(500, true)
expect(transport.state).to_equal("reconnecting")
expect(transport.reconnectAttempts).to_equal(1)  # oracle: value fixed by the spec contract
expect(transport.reconnectTimerActive).to_equal(true)
transport.handleConnectionError(sseReconnectGiveUpMs())
expect(transport.isClosedStatus()).to_equal(true)
```

</details>

#### should reset liveness and reconnect on timeout

- should reset liveness and reconnect on timeout
- Verify: should reset liveness and reconnect on timeout
- Trigger liveness timeout
   - Expected: transport.livenessTimerActive is true
   - Expected: transport.state equals `reconnecting`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reset liveness and reconnect on timeout")
step("Verify: should reset liveness and reconnect on timeout")
# @req: REQ-TOOLS-Sset-001
step("Trigger liveness timeout")
val transport = SSETransport.new("https://api/session/s1/events/stream", "", 0)
transport.connect(200, true)
expect(transport.livenessTimerActive).to_equal(true)
transport.onLivenessTimeout()
expect(transport.state).to_equal("reconnecting")
expect(transport.diagnostics).to_contain("cli_sse_liveness_timeout")
```

</details>

#### should classify post writes by auth and status

- should classify post writes by auth and status
- Verify: should classify post writes by auth and status
- Write with missing auth, permanent error, retry, then success
   - Expected: transport.write("assistant", false, [200]) equals `0`
   - Expected: transport.write("assistant", true, [400]) equals `1`
   - Expected: transport.write("assistant", true, [500, 429, 201]) equals `3`
   - Expected: transport.postedMessages[0] equals `assistant`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should classify post writes by auth and status")
step("Verify: should classify post writes by auth and status")
# @req: REQ-TOOLS-Sset-001
step("Write with missing auth, permanent error, retry, then success")
val transport = SSETransport.new("https://api/session/s1/events/stream", "", 0)
expect(transport.write("assistant", false, [200])).to_equal(0)  # oracle: value fixed by the spec contract
expect(transport.write("assistant", true, [400])).to_equal(1)  # oracle: value fixed by the spec contract
expect(transport.write("assistant", true, [500, 429, 201])).to_equal(3)  # oracle: value fixed by the spec contract
expect(transport.postedMessages[0]).to_equal("assistant")
expect(transport.diagnostics).to_contain("cli_sse_post_no_token")
expect(transport.diagnostics).to_contain("cli_sse_post_client_error")
```

</details>

#### should convert URLs, expose constants, and close timers

- should convert URLs, expose constants, and close timers
- Verify: should convert URLs, expose constants, and close timers
- Pin URL and timeout contract
   - Expected: transport.postUrl equals `https://api.example.com/v2/session_ingress/session/s1/events`
   - Expected: transport.state equals `closing`
   - Expected: transport.reconnectTimerActive is false
   - Expected: transport.livenessTimerActive is false
   - Expected: reconnectDelayMs(6) equals `30000`
   - Expected: postDelayMs(5) equals `8000`
   - Expected: sseLivenessTimeoutMs() equals `45000`
   - Expected: ssePostMaxRetries() equals `10`
   - Expected: sseTransportSourceLinesModeled() equals `710`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should convert URLs, expose constants, and close timers")
step("Verify: should convert URLs, expose constants, and close timers")
# @req: REQ-TOOLS-Sset-001
step("Pin URL and timeout contract")
val transport = SSETransport.new("https://api.example.com/v2/session_ingress/session/s1/events/stream?ignored=1", "", 0)
expect(transport.postUrl).to_equal("https://api.example.com/v2/session_ingress/session/s1/events")
transport.connect(200, true)
transport.reconnectTimerActive = true
transport.close()
expect(transport.state).to_equal("closing")
expect(transport.reconnectTimerActive).to_equal(false)
expect(transport.livenessTimerActive).to_equal(false)
expect(reconnectDelayMs(6)).to_equal(30000)  # oracle: value fixed by the spec contract
expect(postDelayMs(5)).to_equal(8000)  # oracle: value fixed by the spec contract
expect(sseLivenessTimeoutMs()).to_equal(45000)  # oracle: value fixed by the spec contract
expect(ssePostMaxRetries()).to_equal(10)  # oracle: value fixed by the spec contract
expect(sseTransportSourceLinesModeled()).to_equal(710)  # oracle: value fixed by the spec contract
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Sset-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dc656b4ae40a0633a388841a584bc4e629b15a84b897cd9a3a5566355949f206`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc656b4ae40a0633a388841a584bc4e629b15a84b897cd9a3a5566355949f206`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc656b4ae40a0633a388841a584bc4e629b15a84b897cd9a3a5566355949f206`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/cli/transports/SSETransport_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/cli/transports/SSETransport_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/cli/transports/SSETransport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/cli/transports/SSETransport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/cli/transports/SSETransport_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse complete frames and keep incomplete remainder' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/SSETransport_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should parse complete frames and keep incomplete remainder' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/transports/SSETransport_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should connect, read client events, and update sequence high-water mark' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/SSETransport_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should connect, read client events, and update sequence high-water mark' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/transports/SSETransport_spec.spl:51:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should diagnose duplicate, unexpected, and missing-event frames' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/SSETransport_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should diagnose duplicate, unexpected, and missing-event frames' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/transports/SSETransport_spec.spl:65:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should close permanently on permanent connect HTTP status' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/SSETransport_spec.spl:76:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should schedule reconnects and exhaust the reconnect budget' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/transports/SSETransport_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reset liveness and reconnect on timeout' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
