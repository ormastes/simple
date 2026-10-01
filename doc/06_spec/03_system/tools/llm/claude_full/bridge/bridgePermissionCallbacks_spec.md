# Claude Full Bridge Permission Callbacks

> Mirrors `bridge/bridgePermissionCallbacks.ts`: the bridge records permission

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge Permission Callbacks

Mirrors `bridge/bridgePermissionCallbacks.ts`: the bridge records permission

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/bridge/bridgePermissionCallbacks_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `bridge/bridgePermissionCallbacks.ts`: the bridge records permission
requests, validates response behavior, publishes matching responses, returns an
unsubscribe handle, and cancels pending prompts by request id.

## Scenarios

### Claude full bridge permission callbacks

#### validates the required allow or deny behavior discriminant

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- validates the required allow or deny behavior discriminant
- Accept only the two BridgePermissionResponse behavior values from Claude
   - Expected: isBridgePermissionResponse(bridgePermissionResponse("allow", "ok")) is true
   - Expected: isBridgePermissionResponse(bridgePermissionResponse("deny", "no")) is true
   - Expected: isBridgePermissionResponse(bridgePermissionResponse("ask", "unknown")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates the required allow or deny behavior discriminant")
step("Accept only the two BridgePermissionResponse behavior values from Claude")
expect(isBridgePermissionResponse(bridgePermissionResponse("allow", "ok"))).to_equal(true)
expect(isBridgePermissionResponse(bridgePermissionResponse("deny", "no"))).to_equal(true)
expect(isBridgePermissionResponse(bridgePermissionResponse("ask", "unknown"))).to_equal(false)
```

</details>

#### records permission requests with suggestions and blocked path

- records permission requests with suggestions and blocked path
- Send a permission request payload across the bridge shape
   - Expected: callbacks.requestCount() equals `1`
   - Expected: callbacks.requests[0].requestId equals `req_1`
   - Expected: callbacks.requests[0].toolName equals `Bash`
   - Expected: callbacks.requests[0].permissionSuggestions[0].rules[0] equals `Bash(git status)`
   - Expected: callbacks.requests[0].blockedPath equals `/repo/.git`
   - Expected: callbacks.requests[0].canceled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records permission requests with suggestions and blocked path")
step("Send a permission request payload across the bridge shape")
val callbacks = bridgePermissionCallbacksNew()
val suggestion = permissionUpdate("Bash(git status)", "allow", "userSettings")
callbacks.sendRequest("req_1", "Bash", "{\"cmd\":\"git status\"}", "toolu_1", "run git status", [suggestion], "/repo/.git")
expect(callbacks.requestCount()).to_equal(1)
expect(callbacks.requests[0].requestId).to_equal("req_1")
expect(callbacks.requests[0].toolName).to_equal("Bash")
expect(callbacks.requests[0].input).to_contain("git status")
expect(callbacks.requests[0].permissionSuggestions[0].rules[0]).to_equal("Bash(git status)")
expect(callbacks.requests[0].blockedPath).to_equal("/repo/.git")
expect(callbacks.requests[0].canceled).to_equal(false)
```

</details>

#### publishes valid responses and unsubscribe stops later deliveries

- publishes valid responses and unsubscribe stops later deliveries
- Subscribe to one request id and deliver an allow response
   - Expected: callbacks.activeSubscriptionCount() equals `1`
   - Expected: callbacks.sendResponse("req_other", bridgePermissionResponse("allow", "ignored")) is true
   - Expected: callbacks.deliveredCount(unsubscribe.subscriptionId) equals `0`
   - Expected: callbacks.sendResponse("req_2", bridgePermissionResponse("allow", "approved")) is true
   - Expected: callbacks.deliveredCount(unsubscribe.subscriptionId) equals `1`
   - Expected: callbacks.lastDeliveredBehavior(unsubscribe.subscriptionId) equals `allow`
   - Expected: callbacks.lastDeliveredMessage(unsubscribe.subscriptionId) equals `approved`
   - Expected: callbacks.responseCount() equals `2`
- Call the returned unsubscribe handle and reject invalid response behavior
   - Expected: callbacks.unsubscribe(unsubscribe.subscriptionId) is true
   - Expected: callbacks.activeSubscriptionCount() equals `0`
   - Expected: callbacks.sendResponse("req_2", bridgePermissionResponse("deny", "late")) is true
   - Expected: callbacks.deliveredCount(unsubscribe.subscriptionId) equals `1`
   - Expected: callbacks.sendResponse("req_2", bridgePermissionResponse("ask", "bad")) is false
   - Expected: callbacks.responseCount() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("publishes valid responses and unsubscribe stops later deliveries")
step("Subscribe to one request id and deliver an allow response")
val callbacks = bridgePermissionCallbacksNew()
val unsubscribe = callbacks.onResponse("req_2")
expect(callbacks.activeSubscriptionCount()).to_equal(1)
expect(callbacks.sendResponse("req_other", bridgePermissionResponse("allow", "ignored"))).to_equal(true)
expect(callbacks.deliveredCount(unsubscribe.subscriptionId)).to_equal(0)
expect(callbacks.sendResponse("req_2", bridgePermissionResponse("allow", "approved"))).to_equal(true)
expect(callbacks.deliveredCount(unsubscribe.subscriptionId)).to_equal(1)
expect(callbacks.lastDeliveredBehavior(unsubscribe.subscriptionId)).to_equal("allow")
expect(callbacks.lastDeliveredMessage(unsubscribe.subscriptionId)).to_equal("approved")
expect(callbacks.responseCount()).to_equal(2)

step("Call the returned unsubscribe handle and reject invalid response behavior")
expect(callbacks.unsubscribe(unsubscribe.subscriptionId)).to_equal(true)
expect(callbacks.activeSubscriptionCount()).to_equal(0)
expect(callbacks.sendResponse("req_2", bridgePermissionResponse("deny", "late"))).to_equal(true)
expect(callbacks.deliveredCount(unsubscribe.subscriptionId)).to_equal(1)
expect(callbacks.sendResponse("req_2", bridgePermissionResponse("ask", "bad"))).to_equal(false)
expect(callbacks.responseCount()).to_equal(3)
```

</details>

#### cancels a pending control request so the app can dismiss its prompt

- cancels a pending control request so the app can dismiss its prompt
- Mark the matching pending request as canceled
   - Expected: callbacks.cancelRequest("missing") is false
   - Expected: callbacks.cancelRequest("req_cancel") is true
   - Expected: callbacks.requests[0].canceled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("cancels a pending control request so the app can dismiss its prompt")
step("Mark the matching pending request as canceled")
val callbacks = bridgePermissionCallbacksNew()
callbacks.sendRequest("req_cancel", "Edit", "{\"file\":\"a.spl\"}", "toolu_3", "edit file", [], "")
expect(callbacks.cancelRequest("missing")).to_equal(false)
expect(callbacks.cancelRequest("req_cancel")).to_equal(true)
expect(callbacks.requests[0].canceled).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `c5fadb56354ffcb055281986d748eb304242413c765ab3e4044fec4866a0cca5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c5fadb56354ffcb055281986d748eb304242413c765ab3e4044fec4866a0cca5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c5fadb56354ffcb055281986d748eb304242413c765ab3e4044fec4866a0cca5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/llm/claude_full/bridge/bridgePermissionCallbacks_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/bridge/bridgePermissionCallbacks_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/bridge/bridgePermissionCallbacks_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/bridge/bridgePermissionCallbacks_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/bridge/bridgePermissionCallbacks_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/bridge/bridgePermissionCallbacks_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates the required allow or deny behavior discriminant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/bridgePermissionCallbacks_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records permission requests with suggestions and blocked path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/bridge/bridgePermissionCallbacks_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes valid responses and unsubscribe stops later deliveries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
