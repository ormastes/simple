# Claude Full Bridge Permission Callbacks

> Mirrors `bridge/bridgePermissionCallbacks.ts`: the bridge records permission

<!-- sdn-diagram:id=bridgePermissionCallbacks_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bridgePermissionCallbacks_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bridgePermissionCallbacks_spec -> std
bridgePermissionCallbacks_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bridgePermissionCallbacks_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `bridge/bridgePermissionCallbacks.ts`: the bridge records permission
requests, validates response behavior, publishes matching responses, returns an
unsubscribe handle, and cancels pending prompts by request id.

## Scenarios

### Claude full bridge permission callbacks

#### validates the required allow or deny behavior discriminant

- Accept only the two BridgePermissionResponse behavior values from Claude
   - Expected: isBridgePermissionResponse(bridgePermissionResponse("allow", "ok")) is true
   - Expected: isBridgePermissionResponse(bridgePermissionResponse("deny", "no")) is true
   - Expected: isBridgePermissionResponse(bridgePermissionResponse("ask", "unknown")) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Accept only the two BridgePermissionResponse behavior values from Claude")
expect(isBridgePermissionResponse(bridgePermissionResponse("allow", "ok"))).to_equal(true)
expect(isBridgePermissionResponse(bridgePermissionResponse("deny", "no"))).to_equal(true)
expect(isBridgePermissionResponse(bridgePermissionResponse("ask", "unknown"))).to_equal(false)
```

</details>

#### records permission requests with suggestions and blocked path

- Send a permission request payload across the bridge shape
- callbacks sendRequest
   - Expected: callbacks.requestCount() equals `1`
   - Expected: callbacks.requests[0].requestId equals `req_1`
   - Expected: callbacks.requests[0].toolName equals `Bash`
   - Expected: callbacks.requests[0].permissionSuggestions[0].rules[0] equals `Bash(git status)`
   - Expected: callbacks.requests[0].blockedPath equals `/repo/.git`
   - Expected: callbacks.requests[0].canceled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Mark the matching pending request as canceled
- callbacks sendRequest
   - Expected: callbacks.cancelRequest("missing") is false
   - Expected: callbacks.cancelRequest("req_cancel") is true
   - Expected: callbacks.requests[0].canceled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
