# Claude Full SdkControlTransport

> Purpose: should route client sends through callback with server name

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full SdkControlTransport

Purpose: should route client sends through callback with server name

## At a Glance

| Field | Value |
|-------|-------|
| Category | MCP |
| Status | Active |
| Requirements | N/A - strict llm_caret Claude CLI parity lane. |
| Plan | N/A - target selected from strict checker output. |
| Design | N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/SdkControlTransport.ts`. |
| Research | N/A - upstream TypeScript file is the source reference. |
| Source | `test/03_system/tools/llm/claude_full/services/mcp/SdkControlTransport_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should route client sends through callback with server name
Audience: compiler and tooling engineers who maintain this spec

# Claude Full SdkControlTransport

## Overview

Checks the SDK control MCP transport bridge: CLI-side callback routing,
response delivery, SDK-side response forwarding, idempotent close, and
send-after-close failures.

**Requirements:** N/A - strict llm_caret Claude CLI parity lane.
**Plan:** N/A - target selected from strict checker output.
**Design:** N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/SdkControlTransport.ts`.
**Research:** N/A - upstream TypeScript file is the source reference.

## Scenarios

### Claude full SdkControlTransport

#### should route client sends through callback with server name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should route client sends through callback with server name
- Verify: should route client sends through callback with server name
- Send a JSONRPC request from the CLI transport
   - Expected: transport.send("{\"id\":1}") is true
   - Expected: transport.callback.serverNames[0] equals `srv`
   - Expected: transport.callback.messages[0] equals `{"id":1}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should route client sends through callback with server name")
step("Verify: should route client sends through callback with server name")
# @req: REQ-TOOLS-Sdkc-001
step("Send a JSONRPC request from the CLI transport")
val callback = SendMcpMessageCallback.new(["{\"result\":1}"])
val transport = SdkControlClientTransport.new("srv", callback)
expect(transport.send("{\"id\":1}")).to_equal(true)
expect(transport.callback.serverNames[0]).to_equal("srv")
expect(transport.callback.messages[0]).to_equal("{\"id\":1}")
```

</details>

#### should deliver callback responses to client onmessage sink

- should deliver callback responses to client onmessage sink
- Verify: should deliver callback responses to client onmessage sink
- Callback response is recorded as received
   - Expected: transport.receivedMessages[0] equals `{"id":1,"result":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should deliver callback responses to client onmessage sink")
step("Verify: should deliver callback responses to client onmessage sink")
# @req: REQ-TOOLS-Sdkc-001
step("Callback response is recorded as received")
val callback = SendMcpMessageCallback.new(["{\"id\":1,\"result\":true}"])
val transport = SdkControlClientTransport.new("srv", callback)
transport.send("{\"id\":1}")
expect(transport.receivedMessages[0]).to_equal("{\"id\":1,\"result\":true}")
```

</details>

#### should reject client send after close

- should reject client send after close
- Verify: should reject client send after close
- Close the CLI transport then send
   - Expected: transport.send("{\"id\":2}") is false
   - Expected: transport.error equals `Transport is closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject client send after close")
step("Verify: should reject client send after close")
# @req: REQ-TOOLS-Sdkc-001
step("Close the CLI transport then send")
val transport = SdkControlClientTransport.new("srv", SendMcpMessageCallback.new([]))
transport.close()
expect(transport.send("{\"id\":2}")).to_equal(false)
expect(transport.error).to_equal("Transport is closed")
```

</details>

#### should close client transport idempotently

- should close client transport idempotently
- Verify: should close client transport idempotently
- Close twice
   - Expected: transport.isClosed is true
   - Expected: transport.closeCount equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should close client transport idempotently")
step("Verify: should close client transport idempotently")
# @req: REQ-TOOLS-Sdkc-001
step("Close twice")
val transport = SdkControlClientTransport.new("srv", SendMcpMessageCallback.new([]))
transport.close()
transport.close()
expect(transport.isClosed).to_equal(true)
expect(transport.closeCount).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### should forward server responses through callback sink

- should forward server responses through callback sink
- Verify: should forward server responses through callback sink
- SDK server transport sends a response
   - Expected: transport.send("{\"id\":1,\"result\":true}") is true
   - Expected: transport.sentMessages[0] equals `{"id":1,"result":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should forward server responses through callback sink")
step("Verify: should forward server responses through callback sink")
# @req: REQ-TOOLS-Sdkc-001
step("SDK server transport sends a response")
val transport = SdkControlServerTransport.new()
expect(transport.send("{\"id\":1,\"result\":true}")).to_equal(true)
expect(transport.sentMessages[0]).to_equal("{\"id\":1,\"result\":true}")
```

</details>

#### should record inbound server messages

- should record inbound server messages
- Verify: should record inbound server messages
- Query side forwards a control request to server onmessage
   - Expected: transport.inboundMessages[0] equals `{"id":1}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should record inbound server messages")
step("Verify: should record inbound server messages")
# @req: REQ-TOOLS-Sdkc-001
step("Query side forwards a control request to server onmessage")
val transport = SdkControlServerTransport.new()
transport.receive("{\"id\":1}")
expect(transport.inboundMessages[0]).to_equal("{\"id\":1}")
```

</details>

#### should reject server send after close

- should reject server send after close
- Verify: should reject server send after close
- Close the SDK transport then send
   - Expected: transport.send("{\"id\":3}") is false
   - Expected: transport.error equals `Transport is closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject server send after close")
step("Verify: should reject server send after close")
# @req: REQ-TOOLS-Sdkc-001
step("Close the SDK transport then send")
val transport = SdkControlServerTransport.new()
transport.close()
expect(transport.send("{\"id\":3}")).to_equal(false)
expect(transport.error).to_equal("Transport is closed")
```

</details>

#### should close server transport idempotently

- should close server transport idempotently
- Verify: should close server transport idempotently
- Close twice
   - Expected: transport.isClosed is true
   - Expected: transport.closeCount equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should close server transport idempotently")
step("Verify: should close server transport idempotently")
# @req: REQ-TOOLS-Sdkc-001
step("Close twice")
val transport = SdkControlServerTransport.new()
transport.close()
transport.close()
expect(transport.isClosed).to_equal(true)
expect(transport.closeCount).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### should expose source-backed constants

- should expose source-backed constants
- Verify: should expose source-backed constants
- Pin source surface
   - Expected: callback.responses.len() equals `0`
   - Expected: sdkControlTransportSourceLinesModeled() equals `136`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose source-backed constants")
step("Verify: should expose source-backed constants")
# @req: REQ-TOOLS-Sdkc-001
step("Pin source surface")
val callback = SendMcpMessageCallback.new([])
expect(callback.responses.len()).to_equal(0)  # oracle: value fixed by the spec contract
expect(sdkControlTransportSourceLinesModeled()).to_equal(136)  # oracle: value fixed by the spec contract
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `N/A - strict llm_caret Claude CLI parity lane.`
- **Plan:** `N/A - target selected from strict checker output.`
- **Design:** `N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/SdkControlTransport.ts`.`
- **Research:** `N/A - upstream TypeScript file is the source reference.`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Sdkc-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `58d25c7067b7ddc744000c3d1ebe97523f2bc64f5eadab1ec5ca6ce0d184e30a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `58d25c7067b7ddc744000c3d1ebe97523f2bc64f5eadab1ec5ca6ce0d184e30a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `58d25c7067b7ddc744000c3d1ebe97523f2bc64f5eadab1ec5ca6ce0d184e30a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/services/mcp/SdkControlTransport_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/services/mcp/SdkControlTransport_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/services/mcp/SdkControlTransport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/services/mcp/SdkControlTransport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/services/mcp/SdkControlTransport_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should route client sends through callback with server name' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/SdkControlTransport_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should route client sends through callback with server name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/mcp/SdkControlTransport_spec.spl:45:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should deliver callback responses to client onmessage sink' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/SdkControlTransport_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should deliver callback responses to client onmessage sink' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/mcp/SdkControlTransport_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject client send after close' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/SdkControlTransport_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should reject client send after close' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/mcp/SdkControlTransport_spec.spl:67:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should close client transport idempotently' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/SdkControlTransport_spec.spl:79:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should forward server responses through callback sink' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/SdkControlTransport_spec.spl:89:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should record inbound server messages' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
