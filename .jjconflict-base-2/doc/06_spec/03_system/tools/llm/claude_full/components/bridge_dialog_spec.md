# Claude Full Bridge Dialog

> Checks BridgeDialog parity state without terminal rendering.

<!-- sdn-diagram:id=bridge_dialog_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bridge_dialog_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bridge_dialog_spec -> std
bridge_dialog_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bridge_dialog_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge Dialog

Checks BridgeDialog parity state without terminal rendering.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/components/bridge_dialog_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks BridgeDialog parity state without terminal rendering.

## Scenarios

### Claude full BridgeDialog

#### models labels, visibility, and connection state

- Default empty labels to source copy
   - Expected: bridgeDialogProviderLabel(defaults) equals `Claude`
   - Expected: bridgeDialogTargetLabel(defaults) equals `remote app`
   - Expected: bridgeDialogVisible(defaults) is true
   - Expected: bridgeDialogConnectionState(defaults) equals `connecting`
   - Expected: bridgeDialogTitle(defaults) equals `Connect Claude to remote app`
- Hide disconnected dialogs
   - Expected: bridgeDialogVisible(hidden) is false
   - Expected: bridgeDialogTitle(hidden) equals `Bridge dialog hidden`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Default empty labels to source copy")
val defaults = BridgeDialogState.new(true, false, true, "", "", "req_1", "", "")
expect(bridgeDialogProviderLabel(defaults)).to_equal("Claude")
expect(bridgeDialogTargetLabel(defaults)).to_equal("remote app")
expect(bridgeDialogVisible(defaults)).to_equal(true)
expect(bridgeDialogConnectionState(defaults)).to_equal("connecting")
expect(bridgeDialogTitle(defaults)).to_equal("Connect Claude to remote app")

step("Hide disconnected dialogs")
val hidden = BridgeDialogState.new(true, false, false, "Claude", "desktop", "req_2", "", "")
expect(bridgeDialogVisible(hidden)).to_equal(false)
expect(bridgeDialogTitle(hidden)).to_equal("Bridge dialog hidden")
```

</details>

#### summarizes status and error precedence

- Use custom status before generated connected copy
   - Expected: bridgeDialogConnectionState(connected) equals `connected`
   - Expected: bridgeDialogStatusSummary(connected) equals `Waiting for approval`
   - Expected: bridgeDialogCanApprove(connected) is true
- Error state wins over connected state
   - Expected: bridgeDialogConnectionState(failed) equals `failed`
   - Expected: bridgeDialogStatusSummary(failed) equals `Bridge failed: token expired`
   - Expected: bridgeDialogCanApprove(failed) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Use custom status before generated connected copy")
val connected = BridgeDialogState.new(true, true, false, "Claude", "mobile", "req_3", "", "Waiting for approval")
expect(bridgeDialogConnectionState(connected)).to_equal("connected")
expect(bridgeDialogStatusSummary(connected)).to_equal("Waiting for approval")
expect(bridgeDialogCanApprove(connected)).to_equal(true)

step("Error state wins over connected state")
val failed = BridgeDialogState.new(true, true, false, "Claude", "mobile", "req_4", "token expired", "Waiting")
expect(bridgeDialogConnectionState(failed)).to_equal("failed")
expect(bridgeDialogStatusSummary(failed)).to_equal("Bridge failed: token expired")
expect(bridgeDialogCanApprove(failed)).to_equal(false)
```

</details>

#### returns approve and cancel results

- Approve connected bridge
   - Expected: approved.action equals `approve`
   - Expected: approved.approved is true
   - Expected: approved.cancelled is false
   - Expected: approved.requestId equals `req_5`
- Block approve while connecting and allow cancel
   - Expected: blocked.action equals `blocked`
   - Expected: blocked.summary equals `Bridge connecting`
   - Expected: cancelled.action equals `cancel`
   - Expected: cancelled.approved is false
   - Expected: cancelled.cancelled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Approve connected bridge")
val ready = BridgeDialogState.new(true, true, false, "Claude", "desktop", "req_5", "", "")
val approved = bridgeDialogApprove(ready)
expect(approved.action).to_equal("approve")
expect(approved.approved).to_equal(true)
expect(approved.cancelled).to_equal(false)
expect(approved.requestId).to_equal("req_5")
expect(approved.summary).to_contain("desktop")

step("Block approve while connecting and allow cancel")
val pending = BridgeDialogState.new(true, false, true, "Claude", "desktop", "req_6", "", "")
val blocked = bridgeDialogApprove(pending)
expect(blocked.action).to_equal("blocked")
expect(blocked.summary).to_equal("Bridge connecting")
val cancelled = bridgeDialogCancel(pending)
expect(cancelled.action).to_equal("cancel")
expect(cancelled.approved).to_equal(false)
expect(cancelled.cancelled).to_equal(true)
```

</details>

#### exposes source helpers

- Read source helper values
   - Expected: bridgeDialogSource() equals `BridgeDialog`
   - Expected: bridgeDialogSourceLinesModeled() equals `430`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read source helper values")
expect(bridgeDialogSource()).to_equal("BridgeDialog")
expect(bridgeDialogSourceLinesModeled()).to_equal(430)
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
