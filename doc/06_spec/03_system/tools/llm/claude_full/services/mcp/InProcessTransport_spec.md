# Claude Full InProcessTransport

> Purpose: should create linked peers

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full InProcessTransport

Purpose: should create linked peers

## At a Glance

| Field | Value |
|-------|-------|
| Category | MCP |
| Status | Active |
| Requirements | N/A - strict llm_caret Claude CLI parity lane. |
| Plan | N/A - target selected from strict checker output. |
| Design | N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/InProcessTransport.ts`. |
| Research | N/A - upstream TypeScript file is the source reference. |
| Source | `test/03_system/tools/llm/claude_full/services/mcp/InProcessTransport_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should create linked peers
Audience: compiler and tooling engineers who maintain this spec

# Claude Full InProcessTransport

## Overview

Checks the in-process linked MCP transport pair: peer wiring, message delivery,
idempotent close, peer close propagation, and send-after-close failure.

**Requirements:** N/A - strict llm_caret Claude CLI parity lane.
**Plan:** N/A - target selected from strict checker output.
**Design:** N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/InProcessTransport.ts`.
**Research:** N/A - upstream TypeScript file is the source reference.

## Scenarios

### Claude full InProcessTransport

#### should create linked peers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should create linked peers
- Verify: should create linked peers
- Create a linked client/server pair
   - Expected: pair.client.peerIndex equals `1`
   - Expected: pair.server.peerIndex equals `0`
   - Expected: pair.client.closed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should create linked peers")
step("Verify: should create linked peers")
# @req: REQ-TOOLS-Inpr-001
step("Create a linked client/server pair")
val pair = createLinkedTransportPair()
expect(pair.client.peerIndex).to_equal(1)  # oracle: value fixed by the spec contract
expect(pair.server.peerIndex).to_equal(0)  # oracle: value fixed by the spec contract
expect(pair.client.closed).to_equal(false)
```

</details>

#### should deliver client messages to server

- should deliver client messages to server
- Verify: should deliver client messages to server
- Send a message from client to server
   - Expected: pair.clientSend("{\"id\":1}") is true
   - Expected: pair.server.messages[0] equals `{"id":1}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should deliver client messages to server")
step("Verify: should deliver client messages to server")
# @req: REQ-TOOLS-Inpr-001
step("Send a message from client to server")
val pair = createLinkedTransportPair()
expect(pair.clientSend("{\"id\":1}")).to_equal(true)
expect(pair.server.messages[0]).to_equal("{\"id\":1}")
```

</details>

#### should deliver server messages to client

- should deliver server messages to client
- Verify: should deliver server messages to client
- Send a response from server to client
   - Expected: pair.serverSend("{\"result\":true}") is true
   - Expected: pair.client.messages[0] equals `{"result":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should deliver server messages to client")
step("Verify: should deliver server messages to client")
# @req: REQ-TOOLS-Inpr-001
step("Send a response from server to client")
val pair = createLinkedTransportPair()
expect(pair.serverSend("{\"result\":true}")).to_equal(true)
expect(pair.client.messages[0]).to_equal("{\"result\":true}")
```

</details>

#### should close both sides from client

- should close both sides from client
- Verify: should close both sides from client
- Close client and observe peer close
   - Expected: pair.client.closed is true
   - Expected: pair.server.closed is true
   - Expected: pair.client.closeCount equals `1`
   - Expected: pair.server.closeCount equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should close both sides from client")
step("Verify: should close both sides from client")
# @req: REQ-TOOLS-Inpr-001
step("Close client and observe peer close")
val pair = createLinkedTransportPair()
pair.closeClient()
expect(pair.client.closed).to_equal(true)
expect(pair.server.closed).to_equal(true)
expect(pair.client.closeCount).to_equal(1)  # oracle: value fixed by the spec contract
expect(pair.server.closeCount).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### should close both sides from server

- should close both sides from server
- Verify: should close both sides from server
- Close server and observe peer close
   - Expected: pair.client.closed is true
   - Expected: pair.server.closed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should close both sides from server")
step("Verify: should close both sides from server")
# @req: REQ-TOOLS-Inpr-001
step("Close server and observe peer close")
val pair = createLinkedTransportPair()
pair.closeServer()
expect(pair.client.closed).to_equal(true)
expect(pair.server.closed).to_equal(true)
```

</details>

#### should make close idempotent

- should make close idempotent
- Verify: should make close idempotent
- Close the same side twice
   - Expected: pair.client.closeCount equals `1`
   - Expected: pair.server.closeCount equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should make close idempotent")
step("Verify: should make close idempotent")
# @req: REQ-TOOLS-Inpr-001
step("Close the same side twice")
val pair = createLinkedTransportPair()
pair.closeClient()
pair.closeClient()
expect(pair.client.closeCount).to_equal(1)  # oracle: value fixed by the spec contract
expect(pair.server.closeCount).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### should reject send after close

- should reject send after close
- Verify: should reject send after close
- Close and then send
   - Expected: pair.clientSend("{\"id\":2}") is false
   - Expected: pair.client.error equals `Transport is closed`
   - Expected: pair.server.messages.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject send after close")
step("Verify: should reject send after close")
# @req: REQ-TOOLS-Inpr-001
step("Close and then send")
val pair = createLinkedTransportPair()
pair.closeClient()
expect(pair.clientSend("{\"id\":2}")).to_equal(false)
expect(pair.client.error).to_equal("Transport is closed")
expect(pair.server.messages.len()).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

#### should expose source-backed constants

- should expose source-backed constants
- Verify: should expose source-backed constants
- Pin source surface
   - Expected: inProcessTransportSourceLinesModeled() equals `63`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose source-backed constants")
step("Verify: should expose source-backed constants")
# @req: REQ-TOOLS-Inpr-001
step("Pin source surface")
val transport = InProcessTransport.new()
transport.start()
expect(inProcessTransportSourceLinesModeled()).to_equal(63)  # oracle: value fixed by the spec contract
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


## Related Documentation

- **Requirements:** `N/A - strict llm_caret Claude CLI parity lane.`
- **Plan:** `N/A - target selected from strict checker output.`
- **Design:** `N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/InProcessTransport.ts`.`
- **Research:** `N/A - upstream TypeScript file is the source reference.`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Inpr-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7cb2ec22e98ecef7f65e58cc11a6f13302e17a0e6dae3a5dbc27a95fe1e149f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7cb2ec22e98ecef7f65e58cc11a6f13302e17a0e6dae3a5dbc27a95fe1e149f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7cb2ec22e98ecef7f65e58cc11a6f13302e17a0e6dae3a5dbc27a95fe1e149f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/services/mcp/InProcessTransport_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/services/mcp/InProcessTransport_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/services/mcp/InProcessTransport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/services/mcp/InProcessTransport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/services/mcp/InProcessTransport_spec.spl:32:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create linked peers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/InProcessTransport_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should create linked peers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/mcp/InProcessTransport_spec.spl:43:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should deliver client messages to server' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/InProcessTransport_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should deliver client messages to server' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/mcp/InProcessTransport_spec.spl:53:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should deliver server messages to client' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/InProcessTransport_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should deliver server messages to client' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/mcp/InProcessTransport_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should close both sides from client' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/InProcessTransport_spec.spl:76:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should close both sides from server' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/InProcessTransport_spec.spl:87:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should make close idempotent' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
