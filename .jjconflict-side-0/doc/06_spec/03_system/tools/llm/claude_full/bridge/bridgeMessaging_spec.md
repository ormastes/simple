# Claude Full Bridge Messaging

> Deterministic supporting parts-bin evidence for bounded bridge message state,
> routing, controls, and result construction.

| Field | Value |
|---|---|
| Source | `test/03_system/tools/llm/claude_full/bridge/bridgeMessaging_spec.spl` |
| Executable scenarios | 10 |
| Execution in this tranche | 0 scenarios executed |
| Result | Not executed; no PASS is claimed |
| Requirement | N/A; supporting Claude-full parts-bin evidence |

## Scope and Claim Boundary

The scenarios call the real `BoundedUUIDSet`, `handleIngressMessage`,
`handleServerControlRequest`, and `makeResultMessage` owners through direct
assertions and the `BridgeMessagingModel` state/effect seam. They also cover
the seven isolated policies for message, control-response, and control-request
discrimination; eligibility; title extraction; control-key normalization; and
deterministic result UUIDs through real owner behavior.

The trace arrays are deterministic modeled effects. They do not prove that a
live bridge transport read or wrote a message. The upstream TypeScript source is
absent, so this manual does not claim exact upstream parity or shipped CLI/TUI
reachability.

## Frozen Flow

1. **Set up bounded bridge messaging state**
2. **Route inbound and control messages**
3. **Check deduplication responses and state effects**

The canonical fixture, runner, and checker are
`setup_bridge_messaging_fixture`, `run_bridge_message_flow`, and
`check_bridge_message_flow`.

## Scenarios

1. should route deduplicated ingress controls and results through real owners
2. should retain unique UUIDs and evict the oldest slot
3. should reject storage at zero capacity and reset on clear
4. should enforce SDK message and control discriminants
5. should admit only eligible user assistant and local command messages
6. should extract titles only from ordinary human user text
7. should route control malformed user and non-user ingress distinctly
8. should write exact success responses for mutable controls
9. should expose no-transport outbound permission and unknown failures
10. should construct stable success results without sentinel accessors

## Complete Executable SSpec

The folded source is synchronized exactly with the executable helper and
scenario bodies.

<details>
<summary>Executable SSpec</summary>

```simple
fn setup_bridge_messaging_fixture() -> BridgeMessagingModel:
    BridgeMessagingModel.new(3, "cse-1")

fn run_bridge_message_flow(model: BridgeMessagingModel) -> SDKResultSuccess:
    model.markPosted("echo-1")
    model.ingress("user|echo-1|echo")
    model.ingress("user|in-1|hello")
    model.ingress("user|in-1|hello")
    model.control(SDKControlRequest.new("req-init", "initialize"))
    model.control(SDKControlRequest.setModel("req-model", "sonnet"))
    model.result("cse-1")

fn check_bridge_message_flow(model: BridgeMessagingModel, result: SDKResultSuccess):
    val snapshot = model.snapshot()
    expect(model.trace.ingressRoutes).to_equal(["ignored", "inbound", "ignored"])
    expect(model.trace.inboundUUIDs).to_equal(["in-1"])
    expect(model.trace.analyticsEvents).to_equal(["tengu_bridge_message_received"])
    expect(model.trace.controlRequestIds).to_equal(["req-init", "req-model"])
    expect(model.trace.controlSubtypes).to_equal(["initialize", "set_model"])
    expect(model.trace.controlActions).to_equal(["initialize", "set_model:sonnet"])
    expect(model.trace.controlResponses).to_equal([
        "control_response|success|req-init|cse-1",
        "control_response|success|req-model|cse-1",
    ])
    expect(model.trace.resultSessionIds).to_equal(["cse-1"])
    expect(model.trace.resultUUIDs).to_equal(["uuid-cse-1"])
    expect(snapshot.ingressCount).to_equal(3)
    expect(snapshot.ignoredCount).to_equal(2)
    expect(snapshot.inboundCount).to_equal(1)
    expect(snapshot.controlRequestCount).to_equal(2)
    expect(snapshot.controlWriteCount).to_equal(2)
    expect(snapshot.controlErrorCount).to_equal(0)
    expect(snapshot.resultCount).to_equal(1)
    expect(snapshot.postedUUIDCount).to_equal(1)
    expect(snapshot.inboundUUIDCount).to_equal(1)
    expect(result.msgType).to_equal("result")
    expect(result.subtype).to_equal("success")
    expect(result.uuid).to_equal("uuid-cse-1")

describe "Claude full bridge messaging":
    describe "supporting modeled bridge flow":
        it "should route deduplicated ingress controls and results through real owners":
            step("Set up bounded bridge messaging state")
            val model = setup_bridge_messaging_fixture()
            step("Route inbound and control messages")
            val result = run_bridge_message_flow(model)
            step("Check deduplication responses and state effects")
            check_bridge_message_flow(model, result)

    describe "supporting bounded UUID owner behavior":
        it "should retain unique UUIDs and evict the oldest slot":
            step("Set up bounded bridge messaging state")
            val uuids = BoundedUUIDSet.new(2)
            uuids.add("a")
            uuids.add("b")
            uuids.add("a")
            uuids.add("c")
            step("Check deduplication responses and state effects")
            expect(uuids.size()).to_equal(2)
            expect(uuids.has("a")).to_equal(false)
            expect(uuids.has("b")).to_equal(true)
            expect(uuids.has("c")).to_equal(true)
            expect(uuids.ring).to_equal(["c", "b"])
            expect(uuids.writeIdx).to_equal(1)

        it "should reject storage at zero capacity and reset on clear":
            step("Set up bounded bridge messaging state")
            val zero = BoundedUUIDSet.new(0)
            zero.add("ignored")
            val uuids = BoundedUUIDSet.new(2)
            uuids.add("a")
            uuids.clear()
            step("Check deduplication responses and state effects")
            expect(zero.size()).to_equal(0)
            expect(zero.has("ignored")).to_equal(false)
            expect(uuids.size()).to_equal(0)
            expect(uuids.writeIdx).to_equal(0)

    describe "supporting isolated message policy behavior":
        it "should enforce SDK message and control discriminants":
            step("Route inbound and control messages")
            expect([
                isSDKMessageKind("user"),
                isSDKMessageKind(""),
                isSDKControlResponseKind("control_response", true),
                isSDKControlResponseKind("control_response", false),
                isSDKControlRequestKind("control_request", true, true),
                isSDKControlRequestKind("control_request", true, false),
                isSDKControlRequestKind("other", true, true),
            ]).to_equal([true, false, true, false, true, false, false])

        it "should admit only eligible user assistant and local command messages":
            step("Route inbound and control messages")
            val userSource = BridgeMessage.new("user", "", "hi")
            val assistantSource = BridgeMessage.new("assistant", "", "hi")
            val virtualUser = userSource.virtual()
            val virtualAssistant = assistantSource.virtual()
            expect([
                isEligibleBridgeMessage(BridgeMessage.new("user", "", "hi")),
                isEligibleBridgeMessage(BridgeMessage.new("assistant", "", "hi")),
                isEligibleBridgeMessage(BridgeMessage.new("system", "local_command", "/help")),
                isEligibleBridgeMessage(BridgeMessage.new("system", "other", "x")),
                isEligibleBridgeMessage(virtualUser),
                isEligibleBridgeMessage(virtualAssistant),
            ]).to_equal([true, true, true, false, false, false])

        it "should extract titles only from ordinary human user text":
            step("Route inbound and control messages")
            val titleSource = BridgeMessage.new("user", "", "hello")
            val meta = titleSource.meta()
            val toolResult = titleSource.toolResult()
            val compact = titleSource.compactSummary()
            val task = titleSource.fromOrigin("task")
            expect([
                extractTitleText(BridgeMessage.new("user", "", " hello ")),
                extractTitleText(BridgeMessage.new("assistant", "", "hello")),
                extractTitleText(meta),
                extractTitleText(toolResult),
                extractTitleText(compact),
                extractTitleText(task),
                extractTitleText(BridgeMessage.new("user", "", "<ide_opened_file>x</ide_opened_file>")),
            ]).to_equal(["hello", "", "", "", "", "", ""])

    describe "supporting ingress owner behavior":
        it "should route control malformed user and non-user ingress distinctly":
            step("Set up bounded bridge messaging state")
            val model = setup_bridge_messaging_fixture()
            step("Route inbound and control messages")
            val permission = model.ingress("control_response|requestId")
            val control = model.ingress("control_request|req-2|interrupt")
            val malformed = model.ingress("malformed")
            val user = model.ingress("user|user-1|hello")
            val assistant = model.ingress("assistant|assistant-1|hello")
            step("Check deduplication responses and state effects")
            expect(permission.route).to_equal("permission_response")
            expect(permission.response.requestId).to_equal("request_id")
            expect(control.route).to_equal("control_request")
            expect(control.log).to_contain("subtype=interrupt")
            expect(malformed.route).to_equal("ignored")
            expect(malformed.log).to_equal("")
            expect(user.route).to_equal("inbound")
            expect(user.message.content).to_equal("hello")
            expect(assistant.route).to_equal("ignored")
            expect(model.trace.ingressRoutes).to_equal([
                "permission_response",
                "control_request",
                "ignored",
                "inbound",
                "ignored",
            ])
            val snapshot = model.snapshot()
            expect(snapshot.permissionResponseCount).to_equal(1)

    describe "supporting server control owner behavior":
        it "should write exact success responses for mutable controls":
            step("Set up bounded bridge messaging state")
            val model = setup_bridge_messaging_fixture()
            step("Route inbound and control messages")
            val initialize = model.control(SDKControlRequest.new("req-1", "initialize"))
            val setModel = model.control(SDKControlRequest.setModel("req-2", "opus"))
            val thinking = model.control(SDKControlRequest.setMaxThinkingTokens("req-3", 42))
            val permission = model.control(SDKControlRequest.setPermissionMode("req-4", "acceptEdits"))
            val interrupt = model.control(SDKControlRequest.new("req-5", "interrupt"))
            step("Check deduplication responses and state effects")
            expect([
                initialize.action,
                setModel.action,
                thinking.action,
                permission.action,
                interrupt.action,
            ]).to_equal([
                "initialize",
                "set_model:opus",
                "set_max_thinking_tokens:42",
                "set_permission_mode:acceptEdits",
                "interrupt",
            ])
            val snapshot = model.snapshot()
            expect(snapshot.controlWriteCount).to_equal(5)
            expect(snapshot.controlErrorCount).to_equal(0)
            expect(model.trace.controlResponses[0]).to_equal("control_response|success|req-1|cse-1")

        it "should expose no-transport outbound permission and unknown failures":
            step("Set up bounded bridge messaging state")
            val noTransport = BridgeMessagingModel.new(2, "cse-1")
            noTransport.handlers = noTransport.handlers.withoutTransport()
            val outbound = BridgeMessagingModel.new(2, "cse-1")
            outbound.handlers = outbound.handlers.outbound()
            val denied = BridgeMessagingModel.new(2, "cse-1")
            denied.handlers = denied.handlers.permissionError("denied")
            val unknown = BridgeMessagingModel.new(2, "cse-1")
            step("Route inbound and control messages")
            val missing = noTransport.control(SDKControlRequest.new("req-1", "initialize"))
            val allowedInitialize = outbound.control(SDKControlRequest.new("req-2", "initialize"))
            val rejected = outbound.control(SDKControlRequest.new("req-3", "interrupt"))
            val permissionError = denied.control(SDKControlRequest.setPermissionMode("req-4", "bypass"))
            val unknownError = unknown.control(SDKControlRequest.new("req-5", "future"))
            step("Check deduplication responses and state effects")
            expect(missing.wrote).to_equal(false)
            expect(noTransport.trace.controlActions).to_equal(["no_transport"])
            expect(allowedInitialize.response.subtype).to_equal("success")
            expect(rejected.action).to_equal("outbound_only")
            expect(rejected.response.error).to_equal("This session is outbound-only. Enable Remote Control locally to allow inbound control.")
            expect(permissionError.response.error).to_equal("denied")
            expect(unknownError.response.error).to_equal("REPL bridge does not handle control_request subtype: future")
            val outboundSnapshot = outbound.snapshot()
            val deniedSnapshot = denied.snapshot()
            val unknownSnapshot = unknown.snapshot()
            expect(outboundSnapshot.controlErrorCount).to_equal(1)
            expect(deniedSnapshot.controlErrorCount).to_equal(1)
            expect(unknownSnapshot.controlErrorCount).to_equal(1)

    describe "supporting result owner behavior":
        it "should construct stable success results without sentinel accessors":
            step("Set up bounded bridge messaging state")
            val model = setup_bridge_messaging_fixture()
            step("Route inbound and control messages")
            val first = model.result("cse-1")
            val repeated = model.result("cse-1")
            val other = model.result("cse-2")
            step("Check deduplication responses and state effects")
            expect(first.msgType).to_equal("result")
            expect(first.subtype).to_equal("success")
            expect(first.durationMs).to_equal(0)
            expect(first.durationApiMs).to_equal(0)
            expect(first.isError).to_equal(false)
            expect(first.numTurns).to_equal(0)
            expect(first.result).to_equal("")
            expect(first.stopReason).to_equal("")
            expect(first.totalCostUsd).to_equal(0)
            expect(first.sessionId).to_equal("cse-1")
            expect(first.uuid).to_equal("uuid-cse-1")
            expect(repeated.uuid).to_equal(first.uuid)
            expect(other.uuid).to_equal("uuid-cse-2")
            expect(model.trace.resultSessionIds).to_equal(["cse-1", "cse-1", "cse-2"])
            expect(model.trace.resultUUIDs).to_equal(["uuid-cse-1", "uuid-cse-1", "uuid-cse-2"])
            val snapshot = model.snapshot()
            expect(snapshot.resultCount).to_equal(3)
```

</details>
