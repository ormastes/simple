# Claude Full CLI StructuredIO

> Checks structured stdin parsing, control request resolution, duplicate response suppression, permission callback contracts, and source parity constants.

<!-- sdn-diagram:id=structuredIO_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=structuredIO_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

structuredIO_spec -> std
structuredIO_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=structuredIO_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CLI StructuredIO

Checks structured stdin parsing, control request resolution, duplicate response suppression, permission callback contracts, and source parity constants.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/structuredIO_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks structured stdin parsing, control request resolution, duplicate response suppression, permission callback contracts, and source parity constants.

## Scenarios

### Claude full cli StructuredIO

#### reads prepended messages and complete input lines

- Prepended user turns are yielded before stream input and keep_alive is skipped
- io prependUserMessage
   - Expected: io.readAll() equals `["user|queued", "assistant|hello", "system|ready"]`
   - Expected: io.inputClosed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Prepended user turns are yielded before stream input and keep_alive is skipped")
val io = StructuredIO.new(["keep_alive\nassistant|hello\nsys", "tem|ready\n"], false)
io.prependUserMessage("queued")
expect(io.readAll()).to_equal(["user|queued", "assistant|hello", "system|ready"])
expect(io.inputClosed).to_equal(true)
```

</details>

#### applies environment updates and ignores unknown messages

- Environment update messages are side effects, not yielded conversation turns
   - Expected: io.readAll() equals `["user|hi"]`
   - Expected: io.environmentUpdates equals `["TOKEN=abc"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Environment update messages are side effects, not yielded conversation turns")
val io = StructuredIO.new(["update_environment_variables|TOKEN=abc\nunknown|x\nuser|hi\n"], false)
expect(io.readAll()).to_equal(["user|hi"])
expect(io.environmentUpdates).to_equal(["TOKEN=abc"])
```

</details>

#### tracks pending permission requests and resolves control responses

- Control responses resolve pending requests and notify bridge resolution callbacks
- io setOnControlRequestSent
- io setOnControlRequestResolved
   - Expected: io.sendRequest("can_use_tool", "r1", "tool-1", false) equals `pending:r1`
   - Expected: io.getPendingPermissionRequests() equals `["r1"]`
   - Expected: io.outbound equals `["control_request|r1|can_use_tool"]`
   - Expected: io.processLine("control_response|r1|success|allow|tool-1|uuid-1") equals ``
   - Expected: io.resolvedToolUseIds equals `["tool-1"]`
   - Expected: io.lifecycleReports equals `["uuid-1:completed"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Control responses resolve pending requests and notify bridge resolution callbacks")
val io = StructuredIO.new([], false)
io.setOnControlRequestSent(true)
io.setOnControlRequestResolved(true)
expect(io.sendRequest("can_use_tool", "r1", "tool-1", false)).to_equal("pending:r1")
expect(io.getPendingPermissionRequests()).to_equal(["r1"])
expect(io.outbound).to_equal(["control_request|r1|can_use_tool"])
expect(io.processLine("control_response|r1|success|allow|tool-1|uuid-1")).to_equal("")
expect(io.resolvedToolUseIds).to_equal(["tool-1"])
expect(io.lifecycleReports).to_equal(["uuid-1:completed"])
expect(io.resolvedRequests).to_contain("r1")
expect(io.resolvedRequests).to_contain("r1:allow")
```

</details>

#### ignores duplicate resolved tool responses and forwards unexpected ones

- Late duplicate tool_use responses are suppressed; other orphans hit the callback
- io setUnexpectedResponseCallback
- io sendRequest
- io processLine
- io processLine
- io processLine
   - Expected: io.unexpectedResponses equals `["control_response|orphan|success|allow|tool-2|"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Late duplicate tool_use responses are suppressed; other orphans hit the callback")
val io = StructuredIO.new([], false)
io.setUnexpectedResponseCallback(true)
io.sendRequest("can_use_tool", "r1", "tool-1", false)
io.processLine("control_response|r1|success|allow|tool-1|")
io.processLine("control_response|late|success|allow|tool-1|")
io.processLine("control_response|orphan|success|allow|tool-2|")
expect(io.unexpectedResponses).to_equal(["control_response|orphan|success|allow|tool-2|"])
```

</details>

#### injects bridge responses and cancels stale sdk prompt

- Bridge-injected permission responses resolve and enqueue control_cancel_request
- io sendRequest
- io injectControlResponse


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Bridge-injected permission responses resolve and enqueue control_cancel_request")
val io = StructuredIO.new([], false)
io.sendRequest("can_use_tool", "r2", "tool-2", false)
io.injectControlResponse("control_response|r2|success|deny|tool-2|")
expect(io.outbound).to_contain("control_cancel_request|r2")
expect(io.resolvedRequests).to_contain("r2:deny")
```

</details>

#### rejects pending requests on abort or input close

- Abort sends cancel and read close rejects still-pending requests
- io sendRequest
- io abortRequest
- closed sendRequest
- closed readAll
   - Expected: closed.sendRequest("hook_callback", "h2", "", false) equals `error:Stream closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Abort sends cancel and read close rejects still-pending requests")
val io = StructuredIO.new([], false)
io.sendRequest("can_use_tool", "r3", "tool-3", false)
io.abortRequest("r3")
expect(io.outbound).to_contain("control_cancel_request|r3")
expect(io.rejectedRequests).to_contain("r3:AbortError")
val closed = StructuredIO.new([], false)
closed.sendRequest("hook_callback", "h1", "", false)
closed.readAll()
expect(closed.rejectedRequests).to_contain("h1:Tool permission stream closed before response received")
expect(closed.sendRequest("hook_callback", "h2", "", false)).to_equal("error:Stream closed")
```

</details>

#### replays control responses when configured

- Replay mode yields successful control_response messages to the caller
- io sendRequest
   - Expected: io.processLine("control_response|h1|success|{}||") equals `control_response|h1|success|{}||`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Replay mode yields successful control_response messages to the caller")
val io = StructuredIO.new([], true)
io.sendRequest("hook_callback", "h1", "", false)
expect(io.processLine("control_response|h1|success|{}||")).to_equal("control_response|h1|success|{}||")
```

</details>

#### models permission, hook, elicitation, sandbox, and mcp helpers

- Higher-level callbacks use the same control_request plumbing
   - Expected: io.createCanUseTool("Bash", "tool-4", "", "allow", "deny") equals `allow`
   - Expected: io.createHookCallback("cb", "in", "{\"ok\":true}", false) equals `cb:in:{"ok":true}`
   - Expected: io.createHookCallback("cb", "in", "", true) equals `{}`
   - Expected: io.handleElicitation("srv", "choose", "accept", false) equals `srv:choose:accept`
   - Expected: io.handleElicitation("srv", "choose", "accept", true) equals `cancel`
   - Expected: io.createSandboxAskCallback("example.com", "allow") is true
   - Expected: io.sendMcpMessage("srv", "{\"id\":1}", "{\"id\":1,\"result\":{}}") equals `{"id":1,"result":{}}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Higher-level callbacks use the same control_request plumbing")
val io = StructuredIO.new([], false)
expect(io.createCanUseTool("Bash", "tool-4", "", "allow", "deny")).to_equal("allow")
expect(io.createHookCallback("cb", "in", "{\"ok\":true}", false)).to_equal("cb:in:{\"ok\":true}")
expect(io.createHookCallback("cb", "in", "", true)).to_equal("{}")
expect(io.handleElicitation("srv", "choose", "accept", false)).to_equal("srv:choose:accept")
expect(io.handleElicitation("srv", "choose", "accept", true)).to_equal("cancel")
expect(io.createSandboxAskCallback("example.com", "allow")).to_equal(true)
expect(io.sendMcpMessage("srv", "{\"id\":1}", "{\"id\":1,\"result\":{}}")).to_equal("{\"id\":1,\"result\":{}}")
```

</details>

#### exports source-backed pure helpers

- Pin source contracts without depending on Node runtime objects
   - Expected: serializeDecisionReason("", "", false) equals ``
   - Expected: serializeDecisionReason("classifier", "safe", true) equals `safe`
   - Expected: serializeDecisionReason("rule", "x", true) equals ``
   - Expected: serializeDecisionReason("hook", "approved", false) equals `approved`
   - Expected: buildRequiresActionDetails("Bash", "run ls", "", "Bash", "tu", "req", "{}", false) equals `["Bash", "run ls", "tu", "req", "{}"]`
   - Expected: buildRequiresActionDetails("Bash", "", "summary", "Bash", "tu", "req", "{}", false) equals `["Bash", "summary", "tu", "req", "{}"]`
   - Expected: buildRequiresActionDetails("Bash", "", "", "Bash", "tu", "req", "{}", true) equals `["Bash", "Bash", "tu", "req", "{}"]`
   - Expected: executePermissionRequestHooksForSDK("Bash", "tu", "{}", "", "", 0) equals ``
   - Expected: sandboxNetworkAccessToolName() equals `SandboxNetworkAccess`
   - Expected: maxResolvedToolUseIds() equals `1000`
   - Expected: structuredIoSourceLinesModeled() equals `859`
   - Expected: structuredIoClassSourceLine() equals `135`
   - Expected: duplicateControlResponsesAreIgnored() is true
   - Expected: pendingRequestsRejectOnInputClose() is true
   - Expected: prependedLinesAreReadBeforeInput() is true
   - Expected: keepAliveMessagesAreIgnored() is true
   - Expected: environmentUpdatesAreApplied() is true
   - Expected: controlResponsesCanReplayWhenEnabled() is true
   - Expected: sdkPromptRacesPermissionHooks() is true
   - Expected: sandboxAskUsesCanUseToolProtocol() is true
   - Expected: hookCallbackFallsBackToEmptyObject() is true
   - Expected: elicitationFailureCancels() is true
   - Expected: mcpMessageReturnsNestedResponse() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin source contracts without depending on Node runtime objects")
expect(serializeDecisionReason("", "", false)).to_equal("")
expect(serializeDecisionReason("classifier", "safe", true)).to_equal("safe")
expect(serializeDecisionReason("rule", "x", true)).to_equal("")
expect(serializeDecisionReason("hook", "approved", false)).to_equal("approved")
expect(buildRequiresActionDetails("Bash", "run ls", "", "Bash", "tu", "req", "{}", false)).to_equal(["Bash", "run ls", "tu", "req", "{}"])
expect(buildRequiresActionDetails("Bash", "", "summary", "Bash", "tu", "req", "{}", false)).to_equal(["Bash", "summary", "tu", "req", "{}"])
expect(buildRequiresActionDetails("Bash", "", "", "Bash", "tu", "req", "{}", true)).to_equal(["Bash", "Bash", "tu", "req", "{}"])
expect(executePermissionRequestHooksForSDK("Bash", "tu", "{}", "allow", "{\"cmd\":\"ls\"}", 1)).to_contain("allow|")
expect(executePermissionRequestHooksForSDK("Bash", "tu", "{}", "deny", "", 0)).to_contain("deny|")
expect(executePermissionRequestHooksForSDK("Bash", "tu", "{}", "", "", 0)).to_equal("")
expect(sandboxNetworkAccessToolName()).to_equal("SandboxNetworkAccess")
expect(maxResolvedToolUseIds()).to_equal(1000)
expect(structuredIoSourceLinesModeled()).to_equal(859)
expect(structuredIoClassSourceLine()).to_equal(135)
expect(duplicateControlResponsesAreIgnored()).to_equal(true)
expect(pendingRequestsRejectOnInputClose()).to_equal(true)
expect(prependedLinesAreReadBeforeInput()).to_equal(true)
expect(keepAliveMessagesAreIgnored()).to_equal(true)
expect(environmentUpdatesAreApplied()).to_equal(true)
expect(controlResponsesCanReplayWhenEnabled()).to_equal(true)
expect(sdkPromptRacesPermissionHooks()).to_equal(true)
expect(sandboxAskUsesCanUseToolProtocol()).to_equal(true)
expect(hookCallbackFallsBackToEmptyObject()).to_equal(true)
expect(elicitationFailureCancels()).to_equal(true)
expect(mcpMessageReturnsNestedResponse()).to_equal(true)
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


</details>
