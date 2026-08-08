# Claude In Chrome Native Host

> Checks Chrome native host state and message reader behavior.

<!-- sdn-diagram:id=chromeNativeHost_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chromeNativeHost_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chromeNativeHost_spec -> std
chromeNativeHost_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chromeNativeHost_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude In Chrome Native Host

Checks Chrome native host state and message reader behavior.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/claudeInChrome/chromeNativeHost_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks Chrome native host state and message reader behavior.

## Scenarios

### Claude in Chrome native host

#### should start stop and track MCP clients

- var host = ChromeNativeHost new
   - Expected: host.isRunning() is true
   - Expected: host.socketPath equals `/tmp/claude.sock`
- host = host connectMcpClient
   - Expected: host.getClientCount() equals `1`
   - Expected: host.sentChromeMessages[0] equals `mcp_connected`
- host = host disconnectMcpClient
   - Expected: host.getClientCount() equals `0`
   - Expected: host.sentChromeMessages[1] equals `mcp_disconnected`
   - Expected: host.stop().isRunning() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = ChromeNativeHost.new().start("/tmp/claude.sock")
expect(host.isRunning()).to_equal(true)
expect(host.socketPath).to_equal("/tmp/claude.sock")
host = host.connectMcpClient()
expect(host.getClientCount()).to_equal(1)
expect(host.sentChromeMessages[0]).to_equal("mcp_connected")
host = host.disconnectMcpClient(1)
expect(host.getClientCount()).to_equal(0)
expect(host.sentChromeMessages[1]).to_equal("mcp_disconnected")
expect(host.stop().isRunning()).to_equal(false)
```

</details>

#### should handle chrome message types

- var host = ChromeNativeHost new
- host = host handleMessage
- host = host handleMessage
- host = host handleMessage
- host = host handleMessage
- host = host handleMessage
   - Expected: host.sentChromeMessages[1] equals `pong`
   - Expected: host.sentChromeMessages[2] equals `status_response`
   - Expected: host.sentChromeMessages[3] equals `forward_tool_response:1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var host = ChromeNativeHost.new().start("/tmp/claude.sock").connectMcpClient()
host = host.handleMessage("ping")
host = host.handleMessage("get_status")
host = host.handleMessage("tool_response")
host = host.handleMessage("notification")
host = host.handleMessage("bad")
expect(host.sentChromeMessages[1]).to_equal("pong")
expect(host.sentChromeMessages[2]).to_equal("status_response")
expect(host.sentChromeMessages[3]).to_equal("forward_tool_response:1")
expect(host.sentChromeMessages[5]).to_contain("Unknown message type")
```

</details>

#### should read framed chrome messages and close on invalid length

- var reader = ChromeMessageReader new
   - Expected: first.message equals `hello`
   - Expected: second.message equals `world`
   - Expected: second.reader.read().reader.pending is true
   - Expected: invalid.isNull is true
   - Expected: chromeNativeHostSourceLinesModeled() equals `527`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var reader = ChromeMessageReader.new(maxChromeMessageSize()).pushFrame(5, "hello").pushFrame(5, "world")
val first = reader.read()
expect(first.message).to_equal("hello")
val second = first.reader.read()
expect(second.message).to_equal("world")
expect(second.reader.read().reader.pending).to_equal(true)
val invalid = ChromeMessageReader.new(10).pushFrame(11, "too big").read()
expect(invalid.isNull).to_equal(true)
expect(chromeNativeHostSourceLinesModeled()).to_equal(527)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
