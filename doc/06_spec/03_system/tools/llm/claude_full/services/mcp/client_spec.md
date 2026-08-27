# Claude Full MCP Client

> Purpose: should preserve MCP client error identities

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full MCP Client

Purpose: should preserve MCP client error identities

## At a Glance

| Field | Value |
|-------|-------|
| Category | MCP |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/services/mcp/client_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should preserve MCP client error identities
Audience: compiler and tooling engineers who maintain this spec

# Claude Full MCP Client

Checks deterministic MCP client owner behavior for cache isolation, connection
classification and decisions, bounded batching, aggregation counts, and URL
elicitation retry effects.

Requirements: N/A. These scenarios are supporting Claude-full parts-bin
evidence. They do not claim shipped CLI/TUI reachability, live MCP servers,
network requests, process execution, wall-clock sleeps, or upstream-exact
behavior while the pinned upstream source tree is absent.

The synthetic `doRequest`, auto-classifier conversion, and reconnect string
markers are intentionally excluded from acceptance evidence.

## Scenarios

### Claude full MCP client

### supporting error and cache owner behavior

#### should preserve MCP client error identities

- should preserve MCP client error identities
- Verify: should preserve MCP client error identities
- Create authentication, session, and tool-call errors
   - Expected: auth.name equals `McpAuthError`
   - Expected: auth.serverName equals `srv`
   - Expected: expired.name equals `McpSessionExpiredError`
   - Expected: tool.name equals `McpToolCallError`
   - Expected: tool.telemetryMessage equals `safe bad`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve MCP client error identities")
step("Verify: should preserve MCP client error identities")
# @req: REQ-TOOLS-Clie-001
step("Create authentication, session, and tool-call errors")
val auth = McpAuthError.new("srv", "needs auth")
val expired = McpSessionExpiredError.new("srv")
val tool = McpToolCallError_I_VERIFIED_THIS_IS_NOT_CODE_OR_FILEPATHS.new("bad", "safe bad", "meta")
expect(auth.name).to_equal("McpAuthError")
expect(auth.serverName).to_equal("srv")
expect(expired.name).to_equal("McpSessionExpiredError")
expect(expired.message).to_contain("session expired")
expect(tool.name).to_equal("McpToolCallError")
expect(tool.telemetryMessage).to_equal("safe bad")
```

</details>

#### should detect exact expired MCP session boundaries

- should detect exact expired MCP session boundaries
- Verify: should detect exact expired MCP session boundaries
- Classify HTTP and JSON-RPC session expiration inputs


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should detect exact expired MCP session boundaries")
step("Verify: should detect exact expired MCP session boundaries")
# @req: REQ-TOOLS-Clie-001
step("Classify HTTP and JSON-RPC session expiration inputs")
expect([
    isMcpSessionExpiredError(404, -32001, ""),
    isMcpSessionExpiredError(404, 0, "Session not found"),
    isMcpSessionExpiredError(404, 0, "session not found"),
    isMcpSessionExpiredError(500, -32001, "Session not found"),
]).to_equal([true, true, false, false])
```

</details>

#### should isolate authentication cache state per server

- should isolate authentication cache state per server
- Verify: should isolate authentication cache state per server
- Set two server keys and update only one existing entry
   - Expected: cache.keys equals `["alpha", "beta"]`
   - Expected: cache.values equals `[true, true]`
   - Expected: isMcpAuthCached(cache, "alpha") is true
   - Expected: isMcpAuthCached(cache, "beta") is true
   - Expected: isMcpAuthCached(cache, "gamma") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should isolate authentication cache state per server")
step("Verify: should isolate authentication cache state per server")
# @req: REQ-TOOLS-Clie-001
step("Set two server keys and update only one existing entry")
val cache = McpAuthCacheData.new()
setMcpAuthCacheEntry(cache, "alpha", true)
setMcpAuthCacheEntry(cache, "beta", false)
setMcpAuthCacheEntry(cache, "beta", true)
expect(cache.keys).to_equal(["alpha", "beta"])
expect(cache.values).to_equal([true, true])
expect(isMcpAuthCached(cache, "alpha")).to_equal(true)
expect(isMcpAuthCached(cache, "beta")).to_equal(true)
expect(isMcpAuthCached(cache, "gamma")).to_equal(false)
```

</details>

#### should clear authentication cache state without retaining keys

- should clear authentication cache state without retaining keys
- Verify: should clear authentication cache state without retaining keys
- Clear all keyed authentication cache entries
   - Expected: cleared.keys equals `[]`
   - Expected: cleared.values equals `[]`
   - Expected: isMcpAuthCached(cleared, "alpha") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should clear authentication cache state without retaining keys")
step("Verify: should clear authentication cache state without retaining keys")
# @req: REQ-TOOLS-Clie-001
step("Clear all keyed authentication cache entries")
val cache = McpAuthCacheData.new()
setMcpAuthCacheEntry(cache, "alpha", true)
setMcpAuthCacheEntry(cache, "beta", true)
val cleared = clearMcpAuthCache(cache)
expect(cleared.keys).to_equal([])
expect(cleared.values).to_equal([])
expect(isMcpAuthCached(cleared, "alpha")).to_equal(false)
```

</details>

#### should report remote authentication failure details

- should report remote authentication failure details
- Verify: should report remote authentication failure details
- Create a remote authentication failure for one server
   - Expected: failure.name equals `McpAuthError`
   - Expected: failure.serverName equals `remote-a`
   - Expected: failure.message equals `Remote MCP authentication failed with status 401`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should report remote authentication failure details")
step("Verify: should report remote authentication failure details")
# @req: REQ-TOOLS-Clie-001
step("Create a remote authentication failure for one server")
val failure = handleRemoteAuthFailure("remote-a", 401)
expect(failure.name).to_equal("McpAuthError")
expect(failure.serverName).to_equal("remote-a")
expect(failure.message).to_equal("Remote MCP authentication failed with status 401")
```

</details>

### supporting connection owner behavior

#### should distinguish terminal and nonterminal connection failures

- should distinguish terminal and nonterminal connection failures
- Verify: should distinguish terminal and nonterminal connection failures
- Classify terminal startup failures and retryable or unknown failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should distinguish terminal and nonterminal connection failures")
step("Verify: should distinguish terminal and nonterminal connection failures")
# @req: REQ-TOOLS-Clie-001
step("Classify terminal startup failures and retryable or unknown failures")
val refused = classifyMcpConnectionError("connect ECONNREFUSED 127.0.0.1")
val missing = classifyMcpConnectionError("command not found")
val spawned = classifyMcpConnectionError("spawn failed")
val denied = classifyMcpConnectionError("permission denied")
val timeout = classifyMcpConnectionError("connection timeout")
val unknown = classifyMcpConnectionError("protocol response malformed")
expect([
    refused.category,
    missing.category,
    spawned.category,
    denied.category,
    timeout.category,
    unknown.category,
]).to_equal([
    "connection-refused",
    "not-found",
    "spawn-failure",
    "permission-denied",
    "timeout",
    "unknown",
])
expect([
    isTerminalConnectionError("connect ECONNREFUSED 127.0.0.1"),
    isTerminalConnectionError("command not found"),
    isTerminalConnectionError("spawn failed"),
    isTerminalConnectionError("permission denied"),
    isTerminalConnectionError("connection timeout"),
    isTerminalConnectionError("protocol response malformed"),
]).to_equal([true, true, true, true, false, false])
```

</details>

#### should decide connected expired and disconnected client states

- should decide connected expired and disconnected client states
- Verify: should decide connected expired and disconnected client states
- Resolve the complete ensureConnectedClient state triad


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should decide connected expired and disconnected client states")
step("Verify: should decide connected expired and disconnected client states")
# @req: REQ-TOOLS-Clie-001
step("Resolve the complete ensureConnectedClient state triad")
val connected = ensureConnectedClient("connected", "srv")
val expired = ensureConnectedClient("expired", "srv")
val disconnected = ensureConnectedClient("disconnected", "srv")
expect([
    connected.state,
    expired.state,
    disconnected.state,
]).to_equal(["connected", "expired", "disconnected"])
expect([
    connected.action,
    expired.action,
    disconnected.action,
]).to_equal(["reuse", "reject", "connect"])
expect([
    connected.errorName,
    expired.errorName,
    disconnected.errorName,
]).to_equal(["", "McpSessionExpiredError", ""])
expect([
    connected.serverName,
    expired.serverName,
    disconnected.serverName,
]).to_equal(["srv", "srv", "srv"])
```

</details>

#### should clear only the requested server connection cache

- should clear only the requested server connection cache
- Verify: should clear only the requested server connection cache
- Clear one exact server prefix while preserving neighboring names
   - Expected: remaining equals `["alpha-child|http|two", "beta|stdio|three"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should clear only the requested server connection cache")
step("Verify: should clear only the requested server connection cache")
# @req: REQ-TOOLS-Clie-001
step("Clear one exact server prefix while preserving neighboring names")
val remaining = clearServerCache(
    ["alpha|http|one", "alpha-child|http|two", "beta|stdio|three"],
    "alpha",
)
expect(remaining).to_equal(["alpha-child|http|two", "beta|stdio|three"])
```

</details>

#### should compare stable server configuration identity

- should compare stable server configuration identity
- Verify: should compare stable server configuration identity
- Compare matching and changed stable configuration fields
   - Expected: areMcpConfigsEqual(a, b) is true
   - Expected: areMcpConfigsEqual(a, changed) is false
   - Expected: getServerCacheKey(a) equals `display-a|http|https://a|`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should compare stable server configuration identity")
step("Verify: should compare stable server configuration identity")
# @req: REQ-TOOLS-Clie-001
step("Compare matching and changed stable configuration fields")
val a = McpServerConfig.new("display-a", "http")
a.url = "https://a"
a.headers = ["x=1"]
val b = McpServerConfig.new("display-b", "http")
b.url = "https://a"
b.headers = ["x=1"]
val changed = McpServerConfig.new("display-a", "http")
changed.url = "https://b"
changed.headers = ["x=1"]
expect(areMcpConfigsEqual(a, b)).to_equal(true)
expect(areMcpConfigsEqual(a, changed)).to_equal(false)
expect(getServerCacheKey(a)).to_equal("display-a|http|https://a|")
```

</details>

### supporting batch and aggregation owner behavior

#### should preserve item order and exact batch bounds

- should preserve item order and exact batch bounds
- Verify: should preserve item order and exact batch bounds
- Process five items through batches of two
   - Expected: trace.orderedItems equals `["a", "b", "c", "d", "e"]`
   - Expected: trace.normalizedBatchSize equals `2`
   - Expected: trace.batchStarts equals `[0, 2, 4]`
   - Expected: trace.batchEnds equals `[2, 4, 5]`
   - Expected: processBatchedT(["a", "b", "c"], 2) equals `["a", "b", "c"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve item order and exact batch bounds")
step("Verify: should preserve item order and exact batch bounds")
# @req: REQ-TOOLS-Clie-001
step("Process five items through batches of two")
val trace = processBatchedTWithTrace(["a", "b", "c", "d", "e"], 2)
expect(trace.orderedItems).to_equal(["a", "b", "c", "d", "e"])
expect(trace.normalizedBatchSize).to_equal(2)  # oracle: value fixed by the spec contract
expect(trace.batchStarts).to_equal([0, 2, 4])
expect(trace.batchEnds).to_equal([2, 4, 5])
expect(processBatchedT(["a", "b", "c"], 2)).to_equal(["a", "b", "c"])
```

</details>

#### should bound empty oversized and nonpositive batches

- should bound empty oversized and nonpositive batches
- Verify: should bound empty oversized and nonpositive batches
- Normalize nonpositive batch size and avoid empty batch records
   - Expected: empty.batchStarts equals `[]`
   - Expected: empty.batchEnds equals `[]`
   - Expected: oversized.batchStarts equals `[0]`
   - Expected: oversized.batchEnds equals `[2]`
   - Expected: nonpositive.normalizedBatchSize equals `1`
   - Expected: nonpositive.batchStarts equals `[0, 1]`
   - Expected: nonpositive.batchEnds equals `[1, 2]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should bound empty oversized and nonpositive batches")
step("Verify: should bound empty oversized and nonpositive batches")
# @req: REQ-TOOLS-Clie-001
step("Normalize nonpositive batch size and avoid empty batch records")
val empty = processBatchedTWithTrace([], 3)
val oversized = processBatchedTWithTrace(["a", "b"], 10)
val nonpositive = processBatchedTWithTrace(["a", "b"], 0)
expect(empty.batchStarts).to_equal([])
expect(empty.batchEnds).to_equal([])
expect(oversized.batchStarts).to_equal([0])
expect(oversized.batchEnds).to_equal([2])
expect(nonpositive.normalizedBatchSize).to_equal(1)  # oracle: value fixed by the spec contract
expect(nonpositive.batchStarts).to_equal([0, 1])
expect(nonpositive.batchEnds).to_equal([1, 2])
```

</details>

#### should aggregate exact tool command and resource counts

- should aggregate exact tool command and resource counts
- Verify: should aggregate exact tool command and resource counts
- Aggregate distinct ordered MCP capability groups
   - Expected: result.tools equals `["read", "write"]`
   - Expected: result.commands equals `["compact"]`
   - Expected: result.resources equals `["file://a", "file://b", "file://c"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should aggregate exact tool command and resource counts")
step("Verify: should aggregate exact tool command and resource counts")
# @req: REQ-TOOLS-Clie-001
step("Aggregate distinct ordered MCP capability groups")
val result = getMcpToolsCommandsAndResources(
    ["read", "write"],
    ["compact"],
    ["file://a", "file://b", "file://c"],
)
expect(result.tools).to_equal(["read", "write"])
expect(result.commands).to_equal(["compact"])
expect(result.resources).to_equal(["file://a", "file://b", "file://c"])
expect([
    result.toolCount,
    result.commandCount,
    result.resourceCount,
    result.totalCount,
]).to_equal([2, 1, 3, 6])
```

</details>

#### should aggregate empty capability groups without phantom entries

- should aggregate empty capability groups without phantom entries
- Verify: should aggregate empty capability groups without phantom entries
- Aggregate three empty MCP capability groups
   - Expected: result.tools equals `[]`
   - Expected: result.commands equals `[]`
   - Expected: result.resources equals `[]`
   - Expected: result.totalCount equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should aggregate empty capability groups without phantom entries")
step("Verify: should aggregate empty capability groups without phantom entries")
# @req: REQ-TOOLS-Clie-001
step("Aggregate three empty MCP capability groups")
val result = getMcpToolsCommandsAndResources([], [], [])
expect(result.tools).to_equal([])
expect(result.commands).to_equal([])
expect(result.resources).to_equal([])
expect(result.totalCount).to_equal(0)  # oracle: value fixed by the spec contract
```

</details>

### supporting elicitation and result owner behavior

#### should retry URL elicitation exactly once

- should retry URL elicitation exactly once
- Verify: should retry URL elicitation exactly once
- Record an initial URL requirement and one successful retry
   - Expected: result.toolName equals `open-url`
   - Expected: result.attemptCount equals `2`
   - Expected: result.retryCount equals `1`
   - Expected: result.attemptOutcomes equals `["url-required", "ok"]`
   - Expected: result.finalOutcome equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retry URL elicitation exactly once")
step("Verify: should retry URL elicitation exactly once")
# @req: REQ-TOOLS-Clie-001
step("Record an initial URL requirement and one successful retry")
val result = callMCPToolWithUrlElicitationRetry("open-url", true)
expect(result.toolName).to_equal("open-url")
expect(result.attemptCount).to_equal(2)  # oracle: value fixed by the spec contract
expect(result.retryCount).to_equal(1)  # oracle: value fixed by the spec contract
expect(result.attemptOutcomes).to_equal(["url-required", "ok"])
expect(result.finalOutcome).to_equal("ok")
```

</details>

#### should avoid URL elicitation retry after immediate success

- should avoid URL elicitation retry after immediate success
- Verify: should avoid URL elicitation retry after immediate success
- Record one successful tool attempt without elicitation
   - Expected: result.toolName equals `read`
   - Expected: result.attemptCount equals `1`
   - Expected: result.retryCount equals `0`
   - Expected: result.attemptOutcomes equals `["ok"]`
   - Expected: result.finalOutcome equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should avoid URL elicitation retry after immediate success")
step("Verify: should avoid URL elicitation retry after immediate success")
# @req: REQ-TOOLS-Clie-001
step("Record one successful tool attempt without elicitation")
val result = callMCPToolWithUrlElicitationRetry("read", false)
expect(result.toolName).to_equal("read")
expect(result.attemptCount).to_equal(1)  # oracle: value fixed by the spec contract
expect(result.retryCount).to_equal(0)  # oracle: value fixed by the spec contract
expect(result.attemptOutcomes).to_equal(["ok"])
expect(result.finalOutcome).to_equal("ok")
```

</details>

#### should transform MCP result content deterministically

- should transform MCP result content deterministically
- Verify: should transform MCP result content deterministically
- Convert binary content and preserve image classification
   - Expected: result.resultType equals `image`
   - Expected: result.summary equals `hello\nimage`
   - Expected: contentContainsImages(result.content) is true
   - Expected: persistBlobToTextBlock(blob).text equals `[binary blob saved]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should transform MCP result content deterministically")
step("Verify: should transform MCP result content deterministically")
# @req: REQ-TOOLS-Clie-001
step("Convert binary content and preserve image classification")
val textBlock = MCPContentBlock.textBlock("hello")
val imageBlock = MCPContentBlock.image("abc", "image/png")
val result = transformMCPResult([textBlock, imageBlock], false)
expect(result.resultType).to_equal("image")
expect(result.summary).to_equal("hello\nimage")
expect(contentContainsImages(result.content)).to_equal(true)
val blob = MCPContentBlock(typeName: "blob", text: "", mimeType: "application/octet-stream", data: "xx")
expect(persistBlobToTextBlock(blob).text).to_equal("[binary blob saved]")
```

</details>

#### should redact authorization headers without changing other headers

- should redact authorization headers without changing other headers
- Verify: should redact authorization headers without changing other headers
- Redact authorization header values for logging
   - Expected: headers equals `["authorization=[REDACTED]", "x=a"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should redact authorization headers without changing other headers")
step("Verify: should redact authorization headers without changing other headers")
# @req: REQ-TOOLS-Clie-001
step("Redact authorization header values for logging")
val headers = wsHeadersForLogging(["Authorization=Bearer secret", "x=a"])
expect(headers).to_equal(["authorization=[REDACTED]", "x=a"])
```

</details>

#### should preserve deterministic timeout and inclusion policies

- should preserve deterministic timeout and inclusion policies
- Verify: should preserve deterministic timeout and inclusion policies
- Read defaults overrides and the per-server tool allow-list
   - Expected: isLocalMcpServer(config) is true
   - Expected: isIncludedMcpTool(config, "read") is true
   - Expected: isIncludedMcpTool(config, "write") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve deterministic timeout and inclusion policies")
step("Verify: should preserve deterministic timeout and inclusion policies")
# @req: REQ-TOOLS-Clie-001
step("Read defaults overrides and the per-server tool allow-list")
val config = McpServerConfig.new("srv", "stdio")
config.command = "node"
config.includeTools = ["read"]
expect([
    getMcpToolTimeoutMs(""),
    getMcpToolTimeoutMs("500"),
    getConnectionTimeoutMs(""),
    getMcpServerConnectionBatchSize(""),
    getRemoteMcpServerConnectionBatchSize(""),
]).to_equal([120000, 500, 30000, 5, 2])
expect(isLocalMcpServer(config)).to_equal(true)
expect(isIncludedMcpTool(config, "read")).to_equal(true)
expect(isIncludedMcpTool(config, "write")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Clie-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `744bb4f562ebd6fb5e387c646f953522805260d3e468c1a5538e4ffdcfdcf293`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `744bb4f562ebd6fb5e387c646f953522805260d3e468c1a5538e4ffdcfdcf293`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `744bb4f562ebd6fb5e387c646f953522805260d3e468c1a5538e4ffdcfdcf293`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/services/mcp/client_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/services/mcp/client_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/services/mcp/client_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/services/mcp/client_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/services/mcp/client_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve MCP client error identities' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/client_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve MCP client error identities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/mcp/client_spec.spl:52:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should detect exact expired MCP session boundaries' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/client_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should detect exact expired MCP session boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/mcp/client_spec.spl:65:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should isolate authentication cache state per server' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/client_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should isolate authentication cache state per server' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/services/mcp/client_spec.spl:81:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should clear authentication cache state without retaining keys' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/client_spec.spl:95:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report remote authentication failure details' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/services/mcp/client_spec.spl:107:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should distinguish terminal and nonterminal connection failures' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
