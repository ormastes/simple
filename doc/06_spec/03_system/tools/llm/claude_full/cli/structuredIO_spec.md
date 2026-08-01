# Claude Full CLI StructuredIO

> Deterministic supporting parts-bin evidence for the real StructuredIO state
> machine.

| Field | Value |
|---|---|
| Source | `test/03_system/tools/llm/claude_full/cli/structuredIO_spec.spl` |
| Executable scenarios | 16 |
| Execution in this tranche | 0 scenarios executed |
| Result | Not executed; no PASS is claimed |
| Requirement | N/A; supporting Claude-full parts-bin evidence |

## Scope and claim boundary

These scenarios invoke `StructuredIO` directly. No parallel wrapper or shadow
state machine is used. The scope covers ordered input draining, message
routing, pending control responses, duplicate and unexpected responses,
abort/close cleanup, replay, bridge injection, permission precedence, hooks,
elicitation, sandbox asks, MCP messages, and pure display helpers.

This manual does not claim shipped CLI/TUI reachability, Node streams, live MCP
servers, network/process effects, or upstream-exact behavior while the pinned
upstream source tree is absent.

The former source-line and boolean sentinel helpers have been removed. Their
behavioral claims appear here only where a scenario calls the corresponding
real `StructuredIO` method and asserts exact state.

## Frozen helper and visible-flow contract

- `setup_structured_io_fixture` creates the real `StructuredIO`.
- `run_structured_io_flow` delegates directly to `StructuredIO.processLine`.
- `check_structured_io_flow` asserts exact outbound, pending, resolved, and
  rejected arrays.

Every scenario uses these frozen visible steps:

1. Set up structured CLI input state
2. Route one NDJSON or control message
3. Check emitted responses and pending state

## Scenarios

### should drain prepended messages before fragmented input lines

- Prepend `user|queued`.
- Drain fragmented keepalive, assistant, and system input blocks.
- Assert ordered output `user`, `assistant`, `system`, cleared prepended state,
  closed input, and no pending requests.

### should apply environment updates and ignore keepalive and unknown input

- Route keepalive, environment update, unknown, and user messages.
- Assert only the user message is returned, the environment payload is stored,
  and no control state changes.

### should resolve one pending permission response with exact callbacks

- Send one `can_use_tool` request with sent/resolved callbacks enabled.
- Route its successful response with a tool-use ID and lifecycle UUID.
- Assert exact outbound request, empty pending state, resolved tool-use ID,
  lifecycle completion, and ordered callback/result records.

### should reject one pending error response and clear pending state

- Send one hook callback request.
- Route its error response.
- Assert exact error record and empty pending state.

### should suppress duplicates and report only unexpected responses

- Resolve one pending tool response.
- Route a late response for the already-resolved tool and an unrelated orphan.
- Assert the duplicate is suppressed and only the orphan reaches the
  unexpected-response callback.

### should cancel and remove an aborted pending request

- Send then abort one permission request.
- Assert request and cancellation output, one `AbortError`, tracked tool-use
  identity, and fully cleared pending state.

### should reject and remove pending requests when input closes

- Send one hook callback request and close input through `readAll`.
- Assert one stream-closed rejection, empty pending ID/subtype/tool arrays, and
  rejection of new requests after close.

### should reject pre-aborted requests without adding pending state

- Send a request with the abort flag already set.
- Assert `error:Request aborted` with no outbound or pending mutation.

### should replay successful control responses only when enabled

- Route the same success response through replay-enabled and quiet instances.
- Assert only replay mode returns the response while both instances resolve and
  clear pending state identically.

### should resolve bridge-injected responses and cancel the stale SDK prompt

- Send one permission request and inject a bridge response.
- Assert the tool-use ID is resolved, pending state is cleared, and a
  `control_cancel_request` is emitted after the original request.

### should apply force hook and SDK permission precedence

- Compare force, hook, SDK, and default permission decisions.
- Assert exact precedence `force > hook > SDK > deny`.
- Assert exact allow-input update and hook-denial protocol strings.

### should return hook results and fall back to an empty object on failure

- Invoke the real hook callback success and failure paths.
- Assert the exact successful payload and `{}` failure fallback with no control
  state mutation.

### should return elicitation choices and cancel failed elicitation

- Invoke successful and failed elicitation.
- Assert the exact server/message/action result and `cancel` failure result.

### should route sandbox asks through can_use_tool pending state

- Ask for sandbox network access.
- Assert an allowed decision plus exact `can_use_tool` outbound and pending
  request state for `sandbox:example.com`.

### should return nested MCP responses while retaining pending request state

- Send one MCP message with a nested response body.
- Assert exact nested response preservation and exact `mcp_message` outbound
  and pending state.

### should preserve pure decision and display-detail contracts

- Write one outbound line and exercise reason serialization and display-detail
  construction.
- Assert classifier gating, hook reasons, activity/summary/fallback
  descriptions, sandbox tool name, resolved-ID bound, and exact outbound text.

## Removed sentinel mapping

| Removed helper | Direct evidence |
|---|---|
| `structuredIoSourceLinesModeled` | Removed; no behavioral substitute |
| `structuredIoClassSourceLine` | Removed; no behavioral substitute |
| `duplicateControlResponsesAreIgnored` | duplicate/unexpected response scenario |
| `pendingRequestsRejectOnInputClose` | input-close rejection scenario |
| `prependedLinesAreReadBeforeInput` | ordered fragmented-input scenario |
| `keepAliveMessagesAreIgnored` | routing scenario |
| `environmentUpdatesAreApplied` | routing scenario |
| `controlResponsesCanReplayWhenEnabled` | replay-policy scenario |
| `sdkPromptRacesPermissionHooks` | permission-precedence scenario |
| `sandboxAskUsesCanUseToolProtocol` | sandbox pending-state scenario |
| `hookCallbackFallsBackToEmptyObject` | hook outcome scenario |
| `elicitationFailureCancels` | elicitation outcome scenario |
| `mcpMessageReturnsNestedResponse` | nested MCP response scenario |

## Exact pending-state corrections

`StructuredIO.abortRequest` now removes the aborted request ID, subtype, and
tool-use ID after recording cancellation and rejection. `StructuredIO.readAll`
now clears all three pending arrays after rejecting each open request on input
close. These changes make the directly asserted pending-state lifecycle
converge instead of retaining stale requests.

<details>
<summary>Executable helper source</summary>

```simple
fn setup_structured_io_fixture(inputBlocks: [text], replayUserMessages: bool) -> StructuredIO:
    StructuredIO.new(inputBlocks, replayUserMessages)

fn run_structured_io_flow(io: StructuredIO, line: text) -> text:
    io.processLine(line)

fn check_structured_io_flow(io: StructuredIO, expectedOutbound: [text], expectedPending: [text], expectedResolved: [text], expectedRejected: [text]):
    expect(io.outbound).to_equal(expectedOutbound)
    expect(io.pendingRequestIds).to_equal(expectedPending)
    expect(io.resolvedRequests).to_equal(expectedResolved)
    expect(io.rejectedRequests).to_equal(expectedRejected)
```

</details>

## Execution

Run when a qualified pure-Simple runtime is available:

```sh
bin/simple spipe-docgen \
  test/03_system/tools/llm/claude_full/cli/structuredIO_spec.spl \
  --output doc/06_spec --no-index

bin/simple test \
  test/03_system/tools/llm/claude_full/cli/structuredIO_spec.spl \
  --mode=interpreter
```

A missing runtime, nonzero exit, unresolved symbol, no-examples result, or
docgen stub result is a failure. This hand-maintained mirror records zero
executed scenarios and must not be presented as runtime PASS evidence.
