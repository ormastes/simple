# Claude Full MCP Client

> Deterministic supporting parts-bin evidence for isolated MCP client owners.

| Field | Value |
|---|---|
| Source | `test/03_system/tools/llm/claude_full/services/mcp/client_spec.spl` |
| Executable scenarios | 18 |
| Execution in this tranche | 0 scenarios executed |
| Result | Not executed; no PASS is claimed |
| Requirement | N/A; supporting Claude-full parts-bin evidence |

## Scope and claim boundary

This manual mirrors deterministic cache, connection-decision, batching,
aggregation, elicitation, result-transform, redaction, timeout, and inclusion
behavior from `services/mcp/client.spl`. It does not claim shipped CLI/TUI
reachability, a live MCP server, network requests, process execution,
wall-clock sleeps, or upstream-exact behavior while the pinned upstream source
tree is absent.

The synthetic `doRequest`, auto-classifier conversion, and reconnect string
markers were inspected but are deliberately excluded from acceptance evidence.
The batch and elicitation traces record modeled effects; they are not evidence
that external work occurred.

## Scenario parity

### Supporting error and cache owner behavior

#### should preserve MCP client error identities

- Create authentication, session, and tool-call errors.
- Assert the exact auth, expired-session, and safe tool-call identities and
  retained server/telemetry fields.

#### should detect exact expired MCP session boundaries

- Classify HTTP and JSON-RPC session expiration inputs.
- Accept HTTP 404 with code `-32001` or exact `Session not found`; reject wrong
  case and non-404 status.

#### should isolate authentication cache state per server

- Set `alpha` and `beta`, then update only `beta`.
- Assert exact key order, no duplicate key, independent values, and a miss for
  `gamma`.

#### should clear authentication cache state without retaining keys

- Clear two keyed authentication cache entries.
- Assert empty key/value arrays and a subsequent cache miss.

#### should report remote authentication failure details

- Create a remote authentication failure for `remote-a`.
- Assert exact error identity, server, status-bearing message.

### Supporting connection owner behavior

#### should distinguish terminal and nonterminal connection failures

- Classify terminal startup failures and retryable or unknown failures.
- Assert exact categories for refused, missing, spawn, permission, timeout, and
  unknown inputs.
- Assert only the four startup failures are terminal.

#### should decide connected expired and disconnected client states

- Resolve the complete `ensureConnectedClient` state triad.
- Assert exact state/action/error tuples:
  `connected/reuse/""`, `expired/reject/McpSessionExpiredError`, and
  `disconnected/connect/""`.

#### should clear only the requested server connection cache

- Clear the exact `alpha|` cache prefix.
- Preserve `alpha-child|` and `beta|` entries in source order.

#### should compare stable server configuration identity

- Compare matching and changed stable configuration fields.
- Assert display-name differences do not change equality, URL changes do, and
  the cache key retains the configured server identity.

### Supporting batch and aggregation owner behavior

#### should preserve item order and exact batch bounds

- Process five items through batches of two.
- Assert order, normalized size `2`, starts `[0, 2, 4]`, and exclusive ends
  `[2, 4, 5]`.

#### should bound empty oversized and nonpositive batches

- Normalize nonpositive batch size and avoid empty batch records.
- Assert no empty bounds, one oversized bound, and unit bounds after zero
  normalizes to one.

#### should aggregate exact tool command and resource counts

- Aggregate two tools, one command, and three resources.
- Preserve each ordered group and assert counts `[2, 1, 3, 6]`.

#### should aggregate empty capability groups without phantom entries

- Aggregate three empty MCP capability groups.
- Assert empty groups and total count zero.

### Supporting elicitation and result owner behavior

#### should retry URL elicitation exactly once

- Record an initial URL requirement and one successful retry.
- Assert two attempts, one retry, outcomes `["url-required", "ok"]`, and final
  success.

#### should avoid URL elicitation retry after immediate success

- Record one successful tool attempt without elicitation.
- Assert one attempt, zero retries, outcome `["ok"]`, and final success.

#### should transform MCP result content deterministically

- Convert binary content and preserve image classification.
- Assert image schema, exact summary, image detection, and the binary-save
  message.

#### should redact authorization headers without changing other headers

- Redact authorization header values for logging.
- Assert exact redacted and preserved output order.

#### should preserve deterministic timeout and inclusion policies

- Read defaults, an override, and the per-server tool allow-list.
- Assert timeout/batch values `[120000, 500, 30000, 5, 2]`, local stdio
  classification, and exact allow-list behavior.

## Deterministic owner seams

`classifyMcpConnectionError` returns a category plus a terminal flag, and
`isTerminalConnectionError` delegates to that single owner. This prevents the
boolean surface and the reviewable classification from diverging.

`ensureConnectedClient` returns `McpConnectionDecision`, making state, action,
server identity, and typed error identity separately assertable without a
connection attempt.

`processBatchedTWithTrace` records ordered items, normalized batch size, and
zero-based inclusive-start/exclusive-end bounds. `processBatchedT` delegates to
the same trace owner and returns only the ordered values.

`getMcpToolsCommandsAndResources` returns all three ordered groups with their
individual counts and an exact total.

`callMCPToolWithUrlElicitationRetry` records attempt outcomes and retry count.
The modeled URL-required path permits exactly one retry and has no network,
process, timer, or sleep effect.

<details>
<summary>Executable seam and assertion excerpts</summary>

```simple
val refused = classifyMcpConnectionError("connect ECONNREFUSED 127.0.0.1")
val timeout = classifyMcpConnectionError("connection timeout")
expect([refused.category, timeout.category]).to_equal(
    ["connection-refused", "timeout"],
)
expect([
    isTerminalConnectionError("connect ECONNREFUSED 127.0.0.1"),
    isTerminalConnectionError("connection timeout"),
]).to_equal([true, false])

val connected = ensureConnectedClient("connected", "srv")
val expired = ensureConnectedClient("expired", "srv")
val disconnected = ensureConnectedClient("disconnected", "srv")
expect([
    connected.action,
    expired.action,
    disconnected.action,
]).to_equal(["reuse", "reject", "connect"])

val trace = processBatchedTWithTrace(["a", "b", "c", "d", "e"], 2)
expect(trace.orderedItems).to_equal(["a", "b", "c", "d", "e"])
expect(trace.batchStarts).to_equal([0, 2, 4])
expect(trace.batchEnds).to_equal([2, 4, 5])

val aggregate = getMcpToolsCommandsAndResources(
    ["read", "write"],
    ["compact"],
    ["file://a", "file://b", "file://c"],
)
expect([
    aggregate.toolCount,
    aggregate.commandCount,
    aggregate.resourceCount,
    aggregate.totalCount,
]).to_equal([2, 1, 3, 6])

val elicitation = callMCPToolWithUrlElicitationRetry("open-url", true)
expect(elicitation.attemptCount).to_equal(2)
expect(elicitation.retryCount).to_equal(1)
expect(elicitation.attemptOutcomes).to_equal(["url-required", "ok"])
```

</details>

## Execution

Run when a qualified pure-Simple runtime is available:

```sh
bin/simple spipe-docgen \
  test/03_system/tools/llm/claude_full/services/mcp/client_spec.spl \
  --output doc/06_spec --no-index

bin/simple test \
  test/03_system/tools/llm/claude_full/services/mcp/client_spec.spl \
  --mode=interpreter
```

A missing runtime, nonzero exit, unresolved symbol, no-examples result, or
docgen stub result is a failure. This hand-maintained mirror records zero
executed scenarios and must not be presented as runtime PASS evidence.
