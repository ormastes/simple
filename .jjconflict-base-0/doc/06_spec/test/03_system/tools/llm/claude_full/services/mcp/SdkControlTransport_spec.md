# Claude Full SdkControlTransport

> Checks the SDK control MCP transport bridge: CLI-side callback routing, response delivery, SDK-side response forwarding, idempotent close, and send-after-close failures.

<!-- sdn-diagram:id=SdkControlTransport_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=SdkControlTransport_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

SdkControlTransport_spec -> std
SdkControlTransport_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=SdkControlTransport_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full SdkControlTransport

Checks the SDK control MCP transport bridge: CLI-side callback routing, response delivery, SDK-side response forwarding, idempotent close, and send-after-close failures.

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

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

- Send a JSONRPC request from the CLI transport
   - Expected: transport.send("{\"id\":1}") is true
   - Expected: transport.callback.serverNames[0] equals `srv`
   - Expected: transport.callback.messages[0] equals `{"id":1}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Send a JSONRPC request from the CLI transport")
val callback = SendMcpMessageCallback.new(["{\"result\":1}"])
val transport = SdkControlClientTransport.new("srv", callback)
expect(transport.send("{\"id\":1}")).to_equal(true)
expect(transport.callback.serverNames[0]).to_equal("srv")
expect(transport.callback.messages[0]).to_equal("{\"id\":1}")
```

</details>

#### should deliver callback responses to client onmessage sink

- Callback response is recorded as received
- transport send
   - Expected: transport.receivedMessages[0] equals `{"id":1,"result":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Callback response is recorded as received")
val callback = SendMcpMessageCallback.new(["{\"id\":1,\"result\":true}"])
val transport = SdkControlClientTransport.new("srv", callback)
transport.send("{\"id\":1}")
expect(transport.receivedMessages[0]).to_equal("{\"id\":1,\"result\":true}")
```

</details>

#### should reject client send after close

- Close the CLI transport then send
- transport close
   - Expected: transport.send("{\"id\":2}") is false
   - Expected: transport.error equals `Transport is closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Close the CLI transport then send")
val transport = SdkControlClientTransport.new("srv", SendMcpMessageCallback.new([]))
transport.close()
expect(transport.send("{\"id\":2}")).to_equal(false)
expect(transport.error).to_equal("Transport is closed")
```

</details>

#### should close client transport idempotently

- Close twice
- transport close
- transport close
   - Expected: transport.isClosed is true
   - Expected: transport.closeCount equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Close twice")
val transport = SdkControlClientTransport.new("srv", SendMcpMessageCallback.new([]))
transport.close()
transport.close()
expect(transport.isClosed).to_equal(true)
expect(transport.closeCount).to_equal(1)
```

</details>

#### should forward server responses through callback sink

- SDK server transport sends a response
   - Expected: transport.send("{\"id\":1,\"result\":true}") is true
   - Expected: transport.sentMessages[0] equals `{"id":1,"result":true}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("SDK server transport sends a response")
val transport = SdkControlServerTransport.new()
expect(transport.send("{\"id\":1,\"result\":true}")).to_equal(true)
expect(transport.sentMessages[0]).to_equal("{\"id\":1,\"result\":true}")
```

</details>

#### should record inbound server messages

- Query side forwards a control request to server onmessage
- transport receive
   - Expected: transport.inboundMessages[0] equals `{"id":1}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Query side forwards a control request to server onmessage")
val transport = SdkControlServerTransport.new()
transport.receive("{\"id\":1}")
expect(transport.inboundMessages[0]).to_equal("{\"id\":1}")
```

</details>

#### should reject server send after close

- Close the SDK transport then send
- transport close
   - Expected: transport.send("{\"id\":3}") is false
   - Expected: transport.error equals `Transport is closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Close the SDK transport then send")
val transport = SdkControlServerTransport.new()
transport.close()
expect(transport.send("{\"id\":3}")).to_equal(false)
expect(transport.error).to_equal("Transport is closed")
```

</details>

#### should close server transport idempotently

- Close twice
- transport close
- transport close
   - Expected: transport.isClosed is true
   - Expected: transport.closeCount equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Close twice")
val transport = SdkControlServerTransport.new()
transport.close()
transport.close()
expect(transport.isClosed).to_equal(true)
expect(transport.closeCount).to_equal(1)
```

</details>

#### should expose source-backed constants

- Pin source surface
   - Expected: callback.responses.len() equals `0`
   - Expected: sdkControlTransportSourceLinesModeled() equals `136`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin source surface")
val callback = SendMcpMessageCallback.new([])
expect(callback.responses.len()).to_equal(0)
expect(sdkControlTransportSourceLinesModeled()).to_equal(136)
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

- **Requirements:** [N/A - strict llm_caret Claude CLI parity lane.](N/A - strict llm_caret Claude CLI parity lane.)
- **Plan:** [N/A - target selected from strict checker output.](N/A - target selected from strict checker output.)
- **Design:** [N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/SdkControlTransport.ts`.](N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/SdkControlTransport.ts`.)
- **Research:** [N/A - upstream TypeScript file is the source reference.](N/A - upstream TypeScript file is the source reference.)


</details>
