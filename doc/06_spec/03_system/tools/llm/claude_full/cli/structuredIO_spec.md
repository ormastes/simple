# Claude Full CLI StructuredIO

> Checks the real StructuredIO state machine for ordered input, message routing,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CLI StructuredIO

Checks the real StructuredIO state machine for ordered input, message routing,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/cli/structuredIO_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks the real StructuredIO state machine for ordered input, message routing,
pending control requests, replay, bridge injection, permission precedence, and
hook, elicitation, sandbox, and MCP outcomes.

Requirements: N/A. These scenarios are supporting Claude-full parts-bin
evidence. They do not claim shipped CLI/TUI reachability, Node streams, live
MCP servers, network/process effects, or upstream-exact behavior while the
pinned upstream source tree is absent.

## Scenarios

### Claude full CLI StructuredIO

#### should drain prepended messages before fragmented input lines

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should drain prepended messages before fragmented input lines
- Set up structured CLI input state
- Route one NDJSON or control message
- Check emitted responses and pending state
   - Expected: emitted equals `["user|queued", "assistant|hello", "system|ready"]`
   - Expected: io.yieldedMessages equals `emitted`
   - Expected: io.prependedLines equals `[]`
   - Expected: io.inputClosed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should drain prepended messages before fragmented input lines")
step("Set up structured CLI input state")
val io = setup_structured_io_fixture(["keep_alive\nassistant|hello\nsys", "tem|ready\n"], false)
io.prependUserMessage("queued")
step("Route one NDJSON or control message")
val emitted = io.readAll()
step("Check emitted responses and pending state")
expect(emitted).to_equal(["user|queued", "assistant|hello", "system|ready"])
expect(io.yieldedMessages).to_equal(emitted)
expect(io.prependedLines).to_equal([])
expect(io.inputClosed).to_equal(true)
check_structured_io_flow(io, [], [], [], [])
```

</details>

#### should apply environment updates and ignore keepalive and unknown input

- should apply environment updates and ignore keepalive and unknown input
- Set up structured CLI input state
- Route one NDJSON or control message
   - Expected: run_structured_io_flow(io, "keep_alive") equals ``
   - Expected: run_structured_io_flow(io, "update_environment_variables|TOKEN=abc") equals ``
   - Expected: run_structured_io_flow(io, "unknown|x") equals ``
   - Expected: run_structured_io_flow(io, "user|hi") equals `user|hi`
- Check emitted responses and pending state
   - Expected: io.environmentUpdates equals `["TOKEN=abc"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should apply environment updates and ignore keepalive and unknown input")
step("Set up structured CLI input state")
val io = setup_structured_io_fixture([], false)
step("Route one NDJSON or control message")
expect(run_structured_io_flow(io, "keep_alive")).to_equal("")
expect(run_structured_io_flow(io, "update_environment_variables|TOKEN=abc")).to_equal("")
expect(run_structured_io_flow(io, "unknown|x")).to_equal("")
expect(run_structured_io_flow(io, "user|hi")).to_equal("user|hi")
step("Check emitted responses and pending state")
expect(io.environmentUpdates).to_equal(["TOKEN=abc"])
check_structured_io_flow(io, [], [], [], [])
```

</details>

#### should resolve one pending permission response with exact callbacks

- should resolve one pending permission response with exact callbacks
- Set up structured CLI input state
   - Expected: io.sendRequest("can_use_tool", "r1", "tool-1", false) equals `pending:r1`
- Route one NDJSON or control message
- Check emitted responses and pending state
   - Expected: emitted equals ``
   - Expected: io.getPendingPermissionRequests() equals `[]`
   - Expected: io.resolvedToolUseIds equals `["tool-1"]`
   - Expected: io.lifecycleReports equals `["uuid-1:completed"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should resolve one pending permission response with exact callbacks")
step("Set up structured CLI input state")
val io = setup_structured_io_fixture([], false)
io.setOnControlRequestSent(true)
io.setOnControlRequestResolved(true)
expect(io.sendRequest("can_use_tool", "r1", "tool-1", false)).to_equal("pending:r1")
step("Route one NDJSON or control message")
val emitted = run_structured_io_flow(io, "control_response|r1|success|allow|tool-1|uuid-1")
step("Check emitted responses and pending state")
expect(emitted).to_equal("")
expect(io.getPendingPermissionRequests()).to_equal([])
expect(io.resolvedToolUseIds).to_equal(["tool-1"])
expect(io.lifecycleReports).to_equal(["uuid-1:completed"])
check_structured_io_flow(
    io,
    ["control_request|r1|can_use_tool"],
    [],
    ["sent:r1", "r1", "r1:allow"],
    [],
)
```

</details>

#### should reject one pending error response and clear pending state

- should reject one pending error response and clear pending state
- Set up structured CLI input state
- Route one NDJSON or control message
   - Expected: run_structured_io_flow(io, "control_response|h1|error|denied||") equals ``
- Check emitted responses and pending state


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject one pending error response and clear pending state")
step("Set up structured CLI input state")
val io = setup_structured_io_fixture([], false)
io.sendRequest("hook_callback", "h1", "", false)
step("Route one NDJSON or control message")
expect(run_structured_io_flow(io, "control_response|h1|error|denied||")).to_equal("")
step("Check emitted responses and pending state")
check_structured_io_flow(
    io,
    ["control_request|h1|hook_callback"],
    [],
    [],
    ["h1:denied"],
)
```

</details>

#### should suppress duplicates and report only unexpected responses

- should suppress duplicates and report only unexpected responses
- Set up structured CLI input state
- Route one NDJSON or control message
- Check emitted responses and pending state
   - Expected: io.unexpectedResponses equals `["control_response|orphan|success|allow|tool-2|"]`
   - Expected: io.resolvedToolUseIds equals `["tool-1"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should suppress duplicates and report only unexpected responses")
step("Set up structured CLI input state")
val io = setup_structured_io_fixture([], false)
io.setUnexpectedResponseCallback(true)
io.sendRequest("can_use_tool", "r1", "tool-1", false)
step("Route one NDJSON or control message")
run_structured_io_flow(io, "control_response|r1|success|allow|tool-1|")
run_structured_io_flow(io, "control_response|late|success|allow|tool-1|")
run_structured_io_flow(io, "control_response|orphan|success|allow|tool-2|")
step("Check emitted responses and pending state")
expect(io.unexpectedResponses).to_equal(["control_response|orphan|success|allow|tool-2|"])
expect(io.resolvedToolUseIds).to_equal(["tool-1"])
check_structured_io_flow(io, ["control_request|r1|can_use_tool"], [], ["r1:allow"], [])
```

</details>

#### should cancel and remove an aborted pending request

- should cancel and remove an aborted pending request
- Set up structured CLI input state
- Route one NDJSON or control message
- Check emitted responses and pending state
   - Expected: io.resolvedToolUseIds equals `["tool-3"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cancel and remove an aborted pending request")
step("Set up structured CLI input state")
val io = setup_structured_io_fixture([], false)
io.sendRequest("can_use_tool", "r3", "tool-3", false)
step("Route one NDJSON or control message")
io.abortRequest("r3")
step("Check emitted responses and pending state")
expect(io.resolvedToolUseIds).to_equal(["tool-3"])
check_structured_io_flow(
    io,
    ["control_request|r3|can_use_tool", "control_cancel_request|r3"],
    [],
    [],
    ["r3:AbortError"],
)
```

</details>

#### should reject and remove pending requests when input closes

- should reject and remove pending requests when input closes
- Set up structured CLI input state
- Route one NDJSON or control message
   - Expected: io.readAll() equals `[]`
   - Expected: io.sendRequest("hook_callback", "h2", "", false) equals `error:Stream closed`
- Check emitted responses and pending state
   - Expected: io.pendingRequestSubtypes equals `[]`
   - Expected: io.pendingToolUseIds equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject and remove pending requests when input closes")
step("Set up structured CLI input state")
val io = setup_structured_io_fixture([], false)
io.sendRequest("hook_callback", "h1", "", false)
step("Route one NDJSON or control message")
expect(io.readAll()).to_equal([])
expect(io.sendRequest("hook_callback", "h2", "", false)).to_equal("error:Stream closed")
step("Check emitted responses and pending state")
expect(io.pendingRequestSubtypes).to_equal([])
expect(io.pendingToolUseIds).to_equal([])
check_structured_io_flow(
    io,
    ["control_request|h1|hook_callback"],
    [],
    [],
    ["h1:Tool permission stream closed before response received"],
)
```

</details>

#### should reject pre-aborted requests without adding pending state

- should reject pre-aborted requests without adding pending state
- Set up structured CLI input state
- Route one NDJSON or control message
- Check emitted responses and pending state
   - Expected: outcome equals `error:Request aborted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject pre-aborted requests without adding pending state")
step("Set up structured CLI input state")
val io = setup_structured_io_fixture([], false)
step("Route one NDJSON or control message")
val outcome = io.sendRequest("can_use_tool", "r4", "tool-4", true)
step("Check emitted responses and pending state")
expect(outcome).to_equal("error:Request aborted")
check_structured_io_flow(io, [], [], [], [])
```

</details>

#### should replay successful control responses only when enabled

- should replay successful control responses only when enabled
- Set up structured CLI input state
- Route one NDJSON or control message
- Check emitted responses and pending state
   - Expected: replayed equals `line`
   - Expected: suppressed equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should replay successful control responses only when enabled")
step("Set up structured CLI input state")
val replaying = setup_structured_io_fixture([], true)
val quiet = setup_structured_io_fixture([], false)
replaying.sendRequest("hook_callback", "h1", "", false)
quiet.sendRequest("hook_callback", "h1", "", false)
step("Route one NDJSON or control message")
val line = "control_response|h1|success|{}||"
val replayed = run_structured_io_flow(replaying, line)
val suppressed = run_structured_io_flow(quiet, line)
step("Check emitted responses and pending state")
expect(replayed).to_equal(line)
expect(suppressed).to_equal("")
check_structured_io_flow(replaying, ["control_request|h1|hook_callback"], [], ["h1:{}"], [])
check_structured_io_flow(quiet, ["control_request|h1|hook_callback"], [], ["h1:{}"], [])
```

</details>

#### should resolve bridge-injected responses and cancel the stale SDK prompt

- should resolve bridge-injected responses and cancel the stale SDK prompt
- Set up structured CLI input state
- Route one NDJSON or control message
- Check emitted responses and pending state
   - Expected: io.resolvedToolUseIds equals `["tool-2"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should resolve bridge-injected responses and cancel the stale SDK prompt")
step("Set up structured CLI input state")
val io = setup_structured_io_fixture([], false)
io.sendRequest("can_use_tool", "r2", "tool-2", false)
step("Route one NDJSON or control message")
io.injectControlResponse("control_response|r2|success|deny|tool-2|")
step("Check emitted responses and pending state")
expect(io.resolvedToolUseIds).to_equal(["tool-2"])
check_structured_io_flow(
    io,
    ["control_request|r2|can_use_tool", "control_cancel_request|r2"],
    [],
    ["r2:deny"],
    [],
)
```

</details>

#### should apply force hook and SDK permission precedence

- should apply force hook and SDK permission precedence
- Set up structured CLI input state
- Route one NDJSON or control message
- Check emitted responses and pending state
   - Expected: outcomes equals `["deny", "allow", "allow", "deny"]`
   - Expected: executePermissionRequestHooksForSDK("Bash", "tu", "{}", "allow", "{\"cmd\":\"ls\"}", 1) equals `allow|{"cmd":"ls"}|updates:1|reason:hook`
   - Expected: executePermissionRequestHooksForSDK("Bash", "tu", "{}", "deny", "", 0) equals `deny|Permission denied by PermissionRequest hook|reason:hook`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should apply force hook and SDK permission precedence")
step("Set up structured CLI input state")
val io = setup_structured_io_fixture([], false)
step("Route one NDJSON or control message")
val outcomes = [
    io.createCanUseTool("Bash", "tool-4", "deny", "allow", "allow"),
    io.createCanUseTool("Bash", "tool-4", "", "allow", "deny"),
    io.createCanUseTool("Bash", "tool-4", "", "", "allow"),
    io.createCanUseTool("Bash", "tool-4", "", "", ""),
]
step("Check emitted responses and pending state")
expect(outcomes).to_equal(["deny", "allow", "allow", "deny"])
expect(executePermissionRequestHooksForSDK("Bash", "tu", "{}", "allow", "{\"cmd\":\"ls\"}", 1)).to_equal("allow|{\"cmd\":\"ls\"}|updates:1|reason:hook")
expect(executePermissionRequestHooksForSDK("Bash", "tu", "{}", "deny", "", 0)).to_equal("deny|Permission denied by PermissionRequest hook|reason:hook")
check_structured_io_flow(io, [], [], [], [])
```

</details>

#### should return hook results and fall back to an empty object on failure

- should return hook results and fall back to an empty object on failure
- Set up structured CLI input state
- Route one NDJSON or control message
- Check emitted responses and pending state
   - Expected: success equals `cb:in:{"ok":true}`
   - Expected: failure equals `{}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should return hook results and fall back to an empty object on failure")
step("Set up structured CLI input state")
val io = setup_structured_io_fixture([], false)
step("Route one NDJSON or control message")
val success = io.createHookCallback("cb", "in", "{\"ok\":true}", false)
val failure = io.createHookCallback("cb", "in", "ignored", true)
step("Check emitted responses and pending state")
expect(success).to_equal("cb:in:{\"ok\":true}")
expect(failure).to_equal("{}")
check_structured_io_flow(io, [], [], [], [])
```

</details>

#### should return elicitation choices and cancel failed elicitation

- should return elicitation choices and cancel failed elicitation
- Set up structured CLI input state
- Route one NDJSON or control message
- Check emitted responses and pending state
   - Expected: success equals `srv:choose:accept`
   - Expected: failure equals `cancel`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should return elicitation choices and cancel failed elicitation")
step("Set up structured CLI input state")
val io = setup_structured_io_fixture([], false)
step("Route one NDJSON or control message")
val success = io.handleElicitation("srv", "choose", "accept", false)
val failure = io.handleElicitation("srv", "choose", "accept", true)
step("Check emitted responses and pending state")
expect(success).to_equal("srv:choose:accept")
expect(failure).to_equal("cancel")
check_structured_io_flow(io, [], [], [], [])
```

</details>

#### should route sandbox asks through can_use_tool pending state

- should route sandbox asks through can_use_tool pending state
- Set up structured CLI input state
- Route one NDJSON or control message
- Check emitted responses and pending state
   - Expected: allowed is true
   - Expected: io.getPendingPermissionRequests() equals `["sandbox:example.com"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should route sandbox asks through can_use_tool pending state")
step("Set up structured CLI input state")
val io = setup_structured_io_fixture([], false)
step("Route one NDJSON or control message")
val allowed = io.createSandboxAskCallback("example.com", "allow")
step("Check emitted responses and pending state")
expect(allowed).to_equal(true)
expect(io.getPendingPermissionRequests()).to_equal(["sandbox:example.com"])
check_structured_io_flow(
    io,
    ["control_request|sandbox:example.com|can_use_tool"],
    ["sandbox:example.com"],
    [],
    [],
)
```

</details>

#### should return nested MCP responses while retaining pending request state

- should return nested MCP responses while retaining pending request state
- Set up structured CLI input state
- Route one NDJSON or control message
- Check emitted responses and pending state
   - Expected: response equals `{"id":1,"result":{"tools":[]}}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should return nested MCP responses while retaining pending request state")
step("Set up structured CLI input state")
val io = setup_structured_io_fixture([], false)
step("Route one NDJSON or control message")
val response = io.sendMcpMessage("srv", "{\"id\":1}", "{\"id\":1,\"result\":{\"tools\":[]}}")
step("Check emitted responses and pending state")
expect(response).to_equal("{\"id\":1,\"result\":{\"tools\":[]}}")
check_structured_io_flow(
    io,
    ["control_request|mcp:srv|mcp_message"],
    ["mcp:srv"],
    [],
    [],
)
```

</details>

#### should preserve pure decision and display-detail contracts

- should preserve pure decision and display-detail contracts
- Set up structured CLI input state
- Route one NDJSON or control message
- Check emitted responses and pending state
   - Expected: serializeDecisionReason("", "", false) equals ``
   - Expected: serializeDecisionReason("classifier", "safe", true) equals `safe`
   - Expected: serializeDecisionReason("classifier", "safe", false) equals ``
   - Expected: serializeDecisionReason("hook", "approved", false) equals `approved`
   - Expected: buildRequiresActionDetails("Bash", "run ls", "", "Bash", "tu", "req", "{}", false) equals `["Bash", "run ls", "tu", "req", "{}"]`
   - Expected: buildRequiresActionDetails("Bash", "", "summary", "Bash", "tu", "req", "{}", false) equals `["Bash", "summary", "tu", "req", "{}"]`
   - Expected: buildRequiresActionDetails("Bash", "", "", "Bash", "tu", "req", "{}", true) equals `["Bash", "Bash", "tu", "req", "{}"]`
   - Expected: sandboxNetworkAccessToolName() equals `SandboxNetworkAccess`
   - Expected: maxResolvedToolUseIds() equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve pure decision and display-detail contracts")
step("Set up structured CLI input state")
val io = setup_structured_io_fixture([], false)
step("Route one NDJSON or control message")
io.write("safe")
step("Check emitted responses and pending state")
expect(serializeDecisionReason("", "", false)).to_equal("")
expect(serializeDecisionReason("classifier", "safe", true)).to_equal("safe")
expect(serializeDecisionReason("classifier", "safe", false)).to_equal("")
expect(serializeDecisionReason("hook", "approved", false)).to_equal("approved")
expect(buildRequiresActionDetails("Bash", "run ls", "", "Bash", "tu", "req", "{}", false)).to_equal(["Bash", "run ls", "tu", "req", "{}"])
expect(buildRequiresActionDetails("Bash", "", "summary", "Bash", "tu", "req", "{}", false)).to_equal(["Bash", "summary", "tu", "req", "{}"])
expect(buildRequiresActionDetails("Bash", "", "", "Bash", "tu", "req", "{}", true)).to_equal(["Bash", "Bash", "tu", "req", "{}"])
expect(sandboxNetworkAccessToolName()).to_equal("SandboxNetworkAccess")
expect(maxResolvedToolUseIds()).to_equal(1000)
check_structured_io_flow(io, ["safe"], [], [], [])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `259c0dee536b3d02406bba75e2e25b32a2b6bfc13512b7d24f1926e3a8f4d456`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `259c0dee536b3d02406bba75e2e25b32a2b6bfc13512b7d24f1926e3a8f4d456`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `259c0dee536b3d02406bba75e2e25b32a2b6bfc13512b7d24f1926e3a8f4d456`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/cli/structuredIO_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/cli/structuredIO_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/cli/structuredIO_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/cli/structuredIO_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/cli/structuredIO_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/cli/structuredIO_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should drain prepended messages before fragmented input lines' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/structuredIO_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should drain prepended messages before fragmented input lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/structuredIO_spec.spl:53:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should apply environment updates and ignore keepalive and unknown input' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/structuredIO_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should apply environment updates and ignore keepalive and unknown input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/structuredIO_spec.spl:67:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should resolve one pending permission response with exact callbacks' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/structuredIO_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should resolve one pending permission response with exact callbacks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/cli/structuredIO_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should reject one pending error response and clear pending state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/structuredIO_spec.spl:107:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should suppress duplicates and report only unexpected responses' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/cli/structuredIO_spec.spl:123:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should cancel and remove an aborted pending request' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
