# Claude Full InProcessTransport

> Checks the in-process linked MCP transport pair: peer wiring, message delivery, idempotent close, peer close propagation, and send-after-close failure.

<!-- sdn-diagram:id=InProcessTransport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=InProcessTransport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

InProcessTransport_spec -> std
InProcessTransport_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=InProcessTransport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full InProcessTransport

Checks the in-process linked MCP transport pair: peer wiring, message delivery, idempotent close, peer close propagation, and send-after-close failure.

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

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

- Create a linked client/server pair
   - Expected: pair.client.peerIndex equals `1`
   - Expected: pair.server.peerIndex equals `0`
   - Expected: pair.client.closed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create a linked client/server pair")
val pair = createLinkedTransportPair()
expect(pair.client.peerIndex).to_equal(1)
expect(pair.server.peerIndex).to_equal(0)
expect(pair.client.closed).to_equal(false)
```

</details>

#### should deliver client messages to server

- Send a message from client to server
   - Expected: pair.clientSend("{\"id\":1}") is true
   - Expected: pair.server.messages[0] equals `{"id":1}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Send a message from client to server")
val pair = createLinkedTransportPair()
expect(pair.clientSend("{\"id\":1}")).to_equal(true)
expect(pair.server.messages[0]).to_equal("{\"id\":1}")
```

</details>

#### should deliver server messages to client

- Send a response from server to client
   - Expected: pair.serverSend("{\"result\":true}") is true
   - Expected: pair.client.messages[0] equals `{"result":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Send a response from server to client")
val pair = createLinkedTransportPair()
expect(pair.serverSend("{\"result\":true}")).to_equal(true)
expect(pair.client.messages[0]).to_equal("{\"result\":true}")
```

</details>

#### should close both sides from client

- Close client and observe peer close
- pair closeClient
   - Expected: pair.client.closed is true
   - Expected: pair.server.closed is true
   - Expected: pair.client.closeCount equals `1`
   - Expected: pair.server.closeCount equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Close client and observe peer close")
val pair = createLinkedTransportPair()
pair.closeClient()
expect(pair.client.closed).to_equal(true)
expect(pair.server.closed).to_equal(true)
expect(pair.client.closeCount).to_equal(1)
expect(pair.server.closeCount).to_equal(1)
```

</details>

#### should close both sides from server

- Close server and observe peer close
- pair closeServer
   - Expected: pair.client.closed is true
   - Expected: pair.server.closed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Close server and observe peer close")
val pair = createLinkedTransportPair()
pair.closeServer()
expect(pair.client.closed).to_equal(true)
expect(pair.server.closed).to_equal(true)
```

</details>

#### should make close idempotent

- Close the same side twice
- pair closeClient
- pair closeClient
   - Expected: pair.client.closeCount equals `1`
   - Expected: pair.server.closeCount equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Close the same side twice")
val pair = createLinkedTransportPair()
pair.closeClient()
pair.closeClient()
expect(pair.client.closeCount).to_equal(1)
expect(pair.server.closeCount).to_equal(1)
```

</details>

#### should reject send after close

- Close and then send
- pair closeClient
   - Expected: pair.clientSend("{\"id\":2}") is false
   - Expected: pair.client.error equals `Transport is closed`
   - Expected: pair.server.messages.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Close and then send")
val pair = createLinkedTransportPair()
pair.closeClient()
expect(pair.clientSend("{\"id\":2}")).to_equal(false)
expect(pair.client.error).to_equal("Transport is closed")
expect(pair.server.messages.len()).to_equal(0)
```

</details>

#### should expose source-backed constants

- Pin source surface
- transport start
   - Expected: inProcessTransportSourceLinesModeled() equals `63`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin source surface")
val transport = InProcessTransport.new()
transport.start()
expect(inProcessTransportSourceLinesModeled()).to_equal(63)
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

- **Requirements:** [N/A - strict llm_caret Claude CLI parity lane.](N/A - strict llm_caret Claude CLI parity lane.)
- **Plan:** [N/A - target selected from strict checker output.](N/A - target selected from strict checker output.)
- **Design:** [N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/InProcessTransport.ts`.](N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/InProcessTransport.ts`.)
- **Research:** [N/A - upstream TypeScript file is the source reference.](N/A - upstream TypeScript file is the source reference.)


</details>
