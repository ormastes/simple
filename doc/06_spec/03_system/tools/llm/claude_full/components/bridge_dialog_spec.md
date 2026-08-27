# Claude Full Bridge Dialog

> Checks BridgeDialog parity state without terminal rendering.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks BridgeDialog parity state without terminal rendering.

## Scenarios

### Claude full BridgeDialog

#### models labels, visibility, and connection state

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- models labels, visibility, and connection state
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

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("models labels, visibility, and connection state")
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

- summarizes status and error precedence
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

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("summarizes status and error precedence")
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

- returns approve and cancel results
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

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns approve and cancel results")
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

- exposes source helpers
- Read source helper values
   - Expected: bridgeDialogSource() equals `BridgeDialog`
   - Expected: bridgeDialogSourceLinesModeled() equals `430`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exposes source helpers")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1d00cc92706fb549e3b1e2dcde25392986240ecd7a84e017e76b27e8850fa7c7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1d00cc92706fb549e3b1e2dcde25392986240ecd7a84e017e76b27e8850fa7c7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1d00cc92706fb549e3b1e2dcde25392986240ecd7a84e017e76b27e8850fa7c7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/llm/claude_full/components/bridge_dialog_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/components/bridge_dialog_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/components/bridge_dialog_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/components/bridge_dialog_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/components/bridge_dialog_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/components/bridge_dialog_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'models labels, visibility, and connection state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/bridge_dialog_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'summarizes status and error precedence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/components/bridge_dialog_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns approve and cancel results' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
