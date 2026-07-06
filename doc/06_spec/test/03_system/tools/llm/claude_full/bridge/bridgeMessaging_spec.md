# Claude Full Bridge Messaging

> Exercises bridge ingress routing, server control responses, result messages, and UUID deduplication.

<!-- sdn-diagram:id=bridgeMessaging_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bridgeMessaging_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bridgeMessaging_spec -> std
bridgeMessaging_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bridgeMessaging_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge Messaging

Exercises bridge ingress routing, server control responses, result messages, and UUID deduplication.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/bridge/bridgeMessaging_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises bridge ingress routing, server control responses, result messages, and UUID deduplication.

## Scenarios

### Claude full bridge messaging

#### keeps a bounded UUID FIFO ring

- Evict the oldest entry once capacity is reached
- uuids add
- uuids add
- uuids add
   - Expected: uuids.size() equals `2`
   - Expected: uuids.has("a") is true
- uuids add
   - Expected: uuids.has("a") is false
   - Expected: uuids.has("b") is true
   - Expected: uuids.has("c") is true
- uuids clear
   - Expected: uuids.size() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Evict the oldest entry once capacity is reached")
val uuids = BoundedUUIDSet.new(2)
uuids.add("a")
uuids.add("b")
uuids.add("a")
expect(uuids.size()).to_equal(2)
expect(uuids.has("a")).to_equal(true)
uuids.add("c")
expect(uuids.has("a")).to_equal(false)
expect(uuids.has("b")).to_equal(true)
expect(uuids.has("c")).to_equal(true)
uuids.clear()
expect(uuids.size()).to_equal(0)
```

</details>

#### recognizes SDK message and control discriminants

- Type guard equivalents validate discriminants
   - Expected: isSDKMessageKind("user") is true
   - Expected: isSDKMessageKind("") is false
   - Expected: isSDKControlResponseKind("control_response", true) is true
   - Expected: isSDKControlResponseKind("control_response", false) is false
   - Expected: isSDKControlRequestKind("control_request", true, true) is true
   - Expected: isSDKControlRequestKind("control_request", true, false) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Type guard equivalents validate discriminants")
expect(isSDKMessageKind("user")).to_equal(true)
expect(isSDKMessageKind("")).to_equal(false)
expect(isSDKControlResponseKind("control_response", true)).to_equal(true)
expect(isSDKControlResponseKind("control_response", false)).to_equal(false)
expect(isSDKControlRequestKind("control_request", true, true)).to_equal(true)
expect(isSDKControlRequestKind("control_request", true, false)).to_equal(false)
```

</details>

#### filters eligible bridge messages

- Forward user, assistant, and local command messages only
   - Expected: isEligibleBridgeMessage(BridgeMessage.new("user", "", "hi")) is true
   - Expected: isEligibleBridgeMessage(BridgeMessage.new("assistant", "", "hi")) is true
   - Expected: isEligibleBridgeMessage(BridgeMessage.new("system", "local_command", "/help")) is true
   - Expected: isEligibleBridgeMessage(BridgeMessage.new("system", "other", "x")) is false
   - Expected: isEligibleBridgeMessage(BridgeMessage.new("user", "", "hi").virtual()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Forward user, assistant, and local command messages only")
expect(isEligibleBridgeMessage(BridgeMessage.new("user", "", "hi"))).to_equal(true)
expect(isEligibleBridgeMessage(BridgeMessage.new("assistant", "", "hi"))).to_equal(true)
expect(isEligibleBridgeMessage(BridgeMessage.new("system", "local_command", "/help"))).to_equal(true)
expect(isEligibleBridgeMessage(BridgeMessage.new("system", "other", "x"))).to_equal(false)
expect(isEligibleBridgeMessage(BridgeMessage.new("user", "", "hi").virtual())).to_equal(false)
```

</details>

#### extracts title text from human user messages only

- Reject meta, tool result, compact summary, non-human, and display tags
   - Expected: extractTitleText(BridgeMessage.new("user", "", "hello")) equals `hello`
   - Expected: extractTitleText(BridgeMessage.new("assistant", "", "hello")) equals ``
   - Expected: extractTitleText(BridgeMessage.new("user", "", "hello").meta()) equals ``
   - Expected: extractTitleText(BridgeMessage.new("user", "", "hello").toolResult()) equals ``
   - Expected: extractTitleText(BridgeMessage.new("user", "", "hello").compactSummary()) equals ``
   - Expected: extractTitleText(BridgeMessage.new("user", "", "hello").fromOrigin("task")) equals ``
   - Expected: extractTitleText(BridgeMessage.new("user", "", "<ide_opened_file>x</ide_opened_file>")) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reject meta, tool result, compact summary, non-human, and display tags")
expect(extractTitleText(BridgeMessage.new("user", "", "hello"))).to_equal("hello")
expect(extractTitleText(BridgeMessage.new("assistant", "", "hello"))).to_equal("")
expect(extractTitleText(BridgeMessage.new("user", "", "hello").meta())).to_equal("")
expect(extractTitleText(BridgeMessage.new("user", "", "hello").toolResult())).to_equal("")
expect(extractTitleText(BridgeMessage.new("user", "", "hello").compactSummary())).to_equal("")
expect(extractTitleText(BridgeMessage.new("user", "", "hello").fromOrigin("task"))).to_equal("")
expect(extractTitleText(BridgeMessage.new("user", "", "<ide_opened_file>x</ide_opened_file>"))).to_equal("")
```

</details>

#### routes ingress messages and dedups echoes

- Control responses, control requests, echoes, replays, and user messages take separate routes
- posted add
- inbound add
   - Expected: handleIngressMessage("control_response|req_1", posted, inbound).route equals `permission_response`
   - Expected: handleIngressMessage("control_request|req_2|initialize", posted, inbound).route equals `control_request`
   - Expected: handleIngressMessage("user|echo|hi", posted, inbound).route equals `ignored`
   - Expected: handleIngressMessage("user|seen|hi", posted, inbound).route equals `ignored`
   - Expected: result.route equals `inbound`
   - Expected: result.analytics equals `bridgeMessageReceivedEventName()`
   - Expected: result.message.uuid equals `new`
   - Expected: handleIngressMessage("assistant|asst|hello", posted, inbound).route equals `ignored`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Control responses, control requests, echoes, replays, and user messages take separate routes")
val posted = BoundedUUIDSet.new(4)
val inbound = BoundedUUIDSet.new(4)
posted.add("echo")
inbound.add("seen")
expect(handleIngressMessage("control_response|req_1", posted, inbound).route).to_equal("permission_response")
expect(handleIngressMessage("control_request|req_2|initialize", posted, inbound).route).to_equal("control_request")
expect(handleIngressMessage("user|echo|hi", posted, inbound).route).to_equal("ignored")
expect(handleIngressMessage("user|seen|hi", posted, inbound).route).to_equal("ignored")
val result = handleIngressMessage("user|new|hi", posted, inbound)
expect(result.route).to_equal("inbound")
expect(result.analytics).to_equal(bridgeMessageReceivedEventName())
expect(result.message.uuid).to_equal("new")
expect(handleIngressMessage("assistant|asst|hello", posted, inbound).route).to_equal("ignored")
```

</details>

#### responds to server control requests

- Mutable controls succeed when transport is present
   - Expected: handleServerControlRequest(SDKControlRequest.new("req_1", "initialize"), handlers).response.subtype equals `success`
   - Expected: handleServerControlRequest(SDKControlRequest.setModel("req_2", "sonnet"), handlers).action equals `set_model:sonnet`
   - Expected: handleServerControlRequest(SDKControlRequest.setMaxThinkingTokens("req_3", 42), handlers).action equals `set_max_thinking_tokens:42`
   - Expected: handleServerControlRequest(SDKControlRequest.setPermissionMode("req_4", "acceptEdits"), handlers).action equals `set_permission_mode:acceptEdits`
   - Expected: handleServerControlRequest(SDKControlRequest.new("req_5", "interrupt"), handlers).action equals `interrupt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Mutable controls succeed when transport is present")
val handlers = ControlHandlers.new("cse_1")
expect(handleServerControlRequest(SDKControlRequest.new("req_1", "initialize"), handlers).response.subtype).to_equal("success")
expect(handleServerControlRequest(SDKControlRequest.setModel("req_2", "sonnet"), handlers).action).to_equal("set_model:sonnet")
expect(handleServerControlRequest(SDKControlRequest.setMaxThinkingTokens("req_3", 42), handlers).action).to_equal("set_max_thinking_tokens:42")
expect(handleServerControlRequest(SDKControlRequest.setPermissionMode("req_4", "acceptEdits"), handlers).action).to_equal("set_permission_mode:acceptEdits")
expect(handleServerControlRequest(SDKControlRequest.new("req_5", "interrupt"), handlers).action).to_equal("interrupt")
```

</details>

#### returns explicit control errors for unsupported cases

- No transport, outbound-only, permission callback failure, and unknown subtype are visible
   - Expected: handleServerControlRequest(SDKControlRequest.new("req_1", "initialize"), base.withoutTransport()).wrote is false
   - Expected: outbound.response.error equals `outboundOnlyError()`
   - Expected: denied.response.subtype equals `error`
   - Expected: denied.response.error equals `denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("No transport, outbound-only, permission callback failure, and unknown subtype are visible")
val base = ControlHandlers.new("cse_1")
expect(handleServerControlRequest(SDKControlRequest.new("req_1", "initialize"), base.withoutTransport()).wrote).to_equal(false)
val outbound = handleServerControlRequest(SDKControlRequest.new("req_2", "interrupt"), base.outbound())
expect(outbound.response.error).to_equal(outboundOnlyError())
val denied = handleServerControlRequest(SDKControlRequest.setPermissionMode("req_3", "bypass"), base.permissionError("denied"))
expect(denied.response.subtype).to_equal("error")
expect(denied.response.error).to_equal("denied")
val unknown = handleServerControlRequest(SDKControlRequest.new("req_4", "future"), base)
expect(unknown.response.error).to_contain("future")
```

</details>

#### builds result success messages for archival

- Result messages carry empty usage-equivalent fields
   - Expected: result.msgType equals `resultMessageType()`
   - Expected: result.subtype equals `resultSuccessSubtype()`
   - Expected: result.durationMs equals `0`
   - Expected: result.durationApiMs equals `0`
   - Expected: result.isError is false
   - Expected: result.numTurns equals `0`
   - Expected: result.sessionId equals `cse_1`
   - Expected: result.uuid equals `uuid-cse_1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Result messages carry empty usage-equivalent fields")
val result = makeResultMessage("cse_1")
expect(result.msgType).to_equal(resultMessageType())
expect(result.subtype).to_equal(resultSuccessSubtype())
expect(result.durationMs).to_equal(0)
expect(result.durationApiMs).to_equal(0)
expect(result.isError).to_equal(false)
expect(result.numTurns).to_equal(0)
expect(result.sessionId).to_equal("cse_1")
expect(result.uuid).to_equal("uuid-cse_1")
```

</details>

#### exports debug and compatibility constants

- Keep names and log formats aligned with the TypeScript helper
   - Expected: normalizeControlMessageKeys("requestId") equals `request_id`
   - Expected: ingressDebugLine("user", "u1") equals `[bridge:repl] Ingress message type=user uuid=u1`
   - Expected: bridgeReplDebugPrefix() equals `[bridge:repl]`
   - Expected: controlResponseType() equals `control_response`
   - Expected: controlRequestType() equals `control_request`
   - Expected: initializeSubtype() equals `initialize`
   - Expected: setModelSubtype() equals `set_model`
   - Expected: setMaxThinkingTokensSubtype() equals `set_max_thinking_tokens`
   - Expected: setPermissionModeSubtype() equals `set_permission_mode`
   - Expected: interruptSubtype() equals `interrupt`
   - Expected: localCommandSubtype() equals `local_command`
   - Expected: userMessageType() equals `user`
   - Expected: assistantMessageType() equals `assistant`
   - Expected: systemMessageType() equals `system`
   - Expected: boundedUuidSetDefaultCapacity() equals `256`
   - Expected: boundedUuidSetEchoPurpose() equals `echo filtering`
   - Expected: boundedUuidSetInboundPurpose() equals `inbound replay dedup`
   - Expected: ingressControlResponseLog() equals `[bridge:repl] Ingress message type=control_response`
   - Expected: resultDurationMs() equals `0`
   - Expected: resultTotalCostUsd() equals `0`
   - Expected: resultIsError() is false
   - Expected: uuidRingEvictionOrder() equals `oldest`
   - Expected: uuidRingMemoryModel() equals `O(capacity)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Keep names and log formats aligned with the TypeScript helper")
expect(normalizeControlMessageKeys("requestId")).to_equal("request_id")
expect(ingressDebugLine("user", "u1")).to_equal("[bridge:repl] Ingress message type=user uuid=u1")
expect(bridgeReplDebugPrefix()).to_equal("[bridge:repl]")
expect(controlResponseType()).to_equal("control_response")
expect(controlRequestType()).to_equal("control_request")
expect(initializeSubtype()).to_equal("initialize")
expect(setModelSubtype()).to_equal("set_model")
expect(setMaxThinkingTokensSubtype()).to_equal("set_max_thinking_tokens")
expect(setPermissionModeSubtype()).to_equal("set_permission_mode")
expect(interruptSubtype()).to_equal("interrupt")
expect(localCommandSubtype()).to_equal("local_command")
expect(userMessageType()).to_equal("user")
expect(assistantMessageType()).to_equal("assistant")
expect(systemMessageType()).to_equal("system")
expect(boundedUuidSetDefaultCapacity()).to_equal(256)
expect(boundedUuidSetEchoPurpose()).to_equal("echo filtering")
expect(boundedUuidSetInboundPurpose()).to_equal("inbound replay dedup")
expect(ingressControlResponseLog()).to_equal("[bridge:repl] Ingress message type=control_response")
expect(inboundControlRequestLog("initialize")).to_contain("initialize")
expect(echoIgnoredLog("user", "u1")).to_contain("Ignoring echo")
expect(replayIgnoredLog("user", "u1")).to_contain("re-delivered inbound")
expect(nonUserInboundIgnoredLog("assistant")).to_contain("non-user")
expect(noTransportLog()).to_contain("transport not configured")
expect(unknownControlSubtypeError("future")).to_contain("future")
expect(resultDurationMs()).to_equal(0)
expect(resultTotalCostUsd()).to_equal(0)
expect(resultIsError()).to_equal(false)
expect(uuidRingEvictionOrder()).to_equal("oldest")
expect(uuidRingMemoryModel()).to_equal("O(capacity)")
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
