# Claude Full MCP Client

> Checks deterministic parity for the large Claude CLI MCP client surface: typed errors, auth cache, timeout/config helpers, connection classification, tool inclusion, result transforms, and tool-call error mapping.

<!-- sdn-diagram:id=client_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=client_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

client_spec -> std
client_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=client_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full MCP Client

Checks deterministic parity for the large Claude CLI MCP client surface: typed errors, auth cache, timeout/config helpers, connection classification, tool inclusion, result transforms, and tool-call error mapping.

## At a Glance

| Field | Value |
|-------|-------|
| Category | MCP |
| Status | Active |
| Requirements | N/A - strict llm_caret Claude CLI parity lane. |
| Plan | N/A - target selected from strict checker output. |
| Design | N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/client.ts`. |
| Research | N/A - upstream TypeScript file is the source reference. |
| Source | `test/03_system/tools/llm/claude_full/services/mcp/client_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Checks deterministic parity for the large Claude CLI MCP client surface:
typed errors, auth cache, timeout/config helpers, connection classification,
tool inclusion, result transforms, and tool-call error mapping.

**Requirements:** N/A - strict llm_caret Claude CLI parity lane.
**Plan:** N/A - target selected from strict checker output.
**Design:** N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/client.ts`.
**Research:** N/A - upstream TypeScript file is the source reference.

## Scenarios

### Claude full MCP client

#### should expose MCP client error classes

- Create auth, session, and tool-call errors
   - Expected: auth.name equals `McpAuthError`
   - Expected: tool.name equals `McpToolCallError`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create auth, session, and tool-call errors")
val auth = McpAuthError.new("srv", "needs auth")
val expired = McpSessionExpiredError.new("srv")
val tool = McpToolCallError_I_VERIFIED_THIS_IS_NOT_CODE_OR_FILEPATHS.new("bad", "safe bad", "meta")
expect(auth.name).to_equal("McpAuthError")
expect(expired.message).to_contain("session expired")
expect(tool.name).to_equal("McpToolCallError")
```

</details>

#### should detect expired MCP sessions

- Check HTTP and JSON-RPC session expiration
   - Expected: isMcpSessionExpiredError(404, -32001, "Session not found") is true
   - Expected: isMcpSessionExpiredError(500, 0, "oops") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check HTTP and JSON-RPC session expiration")
expect(isMcpSessionExpiredError(404, -32001, "Session not found")).to_equal(true)
expect(isMcpSessionExpiredError(500, 0, "oops")).to_equal(false)
```

</details>

#### should manage auth cache entries

- Set, read, and clear keyed auth cache
   - Expected: isMcpAuthCached(updated, "srv") is true
   - Expected: clearMcpAuthCache(updated).keys.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Set, read, and clear keyed auth cache")
val cache = McpAuthCacheData.new()
val updated = setMcpAuthCacheEntry(cache, "srv", true)
expect(isMcpAuthCached(updated, "srv")).to_equal(true)
expect(clearMcpAuthCache(updated).keys.len()).to_equal(0)
```

</details>

#### should compute timeout and batch defaults

- Read defaults and overrides
   - Expected: getMcpToolTimeoutMs("") equals `120000`
   - Expected: getMcpToolTimeoutMs("500") equals `500`
   - Expected: getConnectionTimeoutMs("") equals `30000`
   - Expected: getMcpServerConnectionBatchSize("") equals `5`
   - Expected: getRemoteMcpServerConnectionBatchSize("") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read defaults and overrides")
expect(getMcpToolTimeoutMs("")).to_equal(120000)
expect(getMcpToolTimeoutMs("500")).to_equal(500)
expect(getConnectionTimeoutMs("")).to_equal(30000)
expect(getMcpServerConnectionBatchSize("")).to_equal(5)
expect(getRemoteMcpServerConnectionBatchSize("")).to_equal(2)
```

</details>

#### should classify servers and included tools

- Check local server and include tool allow-list
   - Expected: isLocalMcpServer(config) is true
   - Expected: isIncludedMcpTool(config, "read") is true
   - Expected: isIncludedMcpTool(config, "write") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Check local server and include tool allow-list")
val config = McpServerConfig.new("srv", "stdio")
config.command = "node"
config.includeTools = ["read"]
expect(isLocalMcpServer(config)).to_equal(true)
expect(isIncludedMcpTool(config, "read")).to_equal(true)
expect(isIncludedMcpTool(config, "write")).to_equal(false)
expect(getServerCacheKey(config)).to_contain("srv|stdio")
```

</details>

#### should redact websocket headers for logging

- Redact authorization header
   - Expected: headers[0] equals `authorization=[REDACTED]`
   - Expected: headers[1] equals `x=a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Redact authorization header")
val headers = wsHeadersForLogging(["Authorization=Bearer secret", "x=a"])
expect(headers[0]).to_equal("authorization=[REDACTED]")
expect(headers[1]).to_equal("x=a")
```

</details>

#### should compare configs and clear server cache

- Compare stable fields
   - Expected: areMcpConfigsEqual(a, b) is true
   - Expected: remaining.len() equals `1`
   - Expected: remaining[0] equals `other|1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare stable fields")
val a = McpServerConfig.new("srv", "http")
a.url = "https://a"
val b = McpServerConfig.new("srv", "http")
b.url = "https://a"
expect(areMcpConfigsEqual(a, b)).to_equal(true)
val remaining = clearServerCache(["srv|1", "other|1"], "srv")
expect(remaining.len()).to_equal(1)
expect(remaining[0]).to_equal("other|1")
```

</details>

#### should transform MCP result content

- Convert blob and detect image schema
   - Expected: result.resultType equals `image`
   - Expected: contentContainsImages(result.content) is true
   - Expected: persistBlobToTextBlock(blob).text equals `[binary blob saved]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Convert blob and detect image schema")
val textBlock = MCPContentBlock.textBlock("hello")
val imageBlock = MCPContentBlock.image("abc", "image/png")
val result = transformMCPResult([textBlock, imageBlock], false)
expect(result.resultType).to_equal("image")
expect(contentContainsImages(result.content)).to_equal(true)
val blob = MCPContentBlock(typeName: "blob", text: "", mimeType: "application/octet-stream", data: "xx")
expect(persistBlobToTextBlock(blob).text).to_equal("[binary blob saved]")
```

</details>

#### should map tool calls to typed outcomes

- Call tool status helpers
   - Expected: callMCPTool("srv", "read", "needs-auth") equals `McpAuthError`
   - Expected: callMCPTool("srv", "read", "expired") equals `McpSessionExpiredError`
   - Expected: processed.result.summary equals `bad`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Call tool status helpers")
expect(callMCPTool("srv", "read", "needs-auth")).to_equal("McpAuthError")
expect(callMCPTool("srv", "read", "expired")).to_equal("McpSessionExpiredError")
val processed = processMCPResult("srv", "read", [MCPContentBlock.textBlock("bad")], true, "meta")
expect(processed.result.summary).to_equal("bad")
```

</details>

#### should expose source-backed helpers

- Pin helper surface
   - Expected: mcpBaseUrlAnalytics("https://mcp.example/path") equals `mcp.example`
   - Expected: extractToolUseId("x tool_use_id=abc") equals `abc`
   - Expected: setupSdkMcpClients([McpServerConfig.new("a", "http")]) equals `1`
   - Expected: mcpClientSourceLinesModeled() equals `3348`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin helper surface")
expect(mcpBaseUrlAnalytics("https://mcp.example/path")).to_equal("mcp.example")
expect(extractToolUseId("x tool_use_id=abc")).to_equal("abc")
expect(setupSdkMcpClients([McpServerConfig.new("a", "http")])).to_equal(1)
expect(mcpClientSourceLinesModeled()).to_equal(3348)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [N/A - strict llm_caret Claude CLI parity lane.](N/A - strict llm_caret Claude CLI parity lane.)
- **Plan:** [N/A - target selected from strict checker output.](N/A - target selected from strict checker output.)
- **Design:** [N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/client.ts`.](N/A - source mirror for `tmp/claude/claude-code-main/src/services/mcp/client.ts`.)
- **Research:** [N/A - upstream TypeScript file is the source reference.](N/A - upstream TypeScript file is the source reference.)


</details>
