# Claude Full Bridge Command

> Checks the Simple model for Claude's `/remote-control` command metadata,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Bridge Command

Checks the Simple model for Claude's `/remote-control` command metadata,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/bridge_command_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks the Simple model for Claude's `/remote-control` command metadata,
state transitions, dialog choices, and prerequisite ordering.

REQ-LLM-CARET-HIDDEN-008 applies to the command admission and prerequisite
scenarios in this parts-bin spec. It does not establish shipped Caret
CLI/TUI reachability.

## Scenarios

### REQ-LLM-CARET-HIDDEN-008: bridge command admission

#### should expose remote-control command metadata and gate hidden state

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose remote-control command metadata and gate hidden state
- Read command metadata
   - Expected: command.typeName equals `local-jsx`
   - Expected: command.name equals `remote-control`
   - Expected: command.aliases.len() equals `1`
   - Expected: command.aliases[0] equals `rc`
   - Expected: command.description equals `Connect this terminal for remote-control sessions`
   - Expected: command.argumentHint equals `[name]`
   - Expected: command.immediate is true
   - Expected: command.isEnabled() is true
   - Expected: command.isHidden() is false
- Disable each command gate
   - Expected: bridgeCommandFor(false, true).isEnabled() is false
   - Expected: bridgeCommandFor(true, false).isHidden() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-LLM-CARET-HIDDEN-008
# @req REQ-SSPEC-SYSTEM
step("should expose remote-control command metadata and gate hidden state")
step("Read command metadata")
val command = bridgeCommand()
expect(command.typeName).to_equal("local-jsx")
expect(command.name).to_equal("remote-control")
expect(command.aliases.len()).to_equal(1)
expect(command.aliases[0]).to_equal("rc")
expect(command.description).to_equal("Connect this terminal for remote-control sessions")
expect(command.argumentHint).to_equal("[name]")
expect(command.immediate).to_equal(true)
expect(command.isEnabled()).to_equal(true)
expect(command.isHidden()).to_equal(false)

step("Disable each command gate")
expect(bridgeCommandFor(false, true).isEnabled()).to_equal(false)
expect(bridgeCommandFor(true, false).isHidden()).to_equal(true)
```

</details>

### supporting bridge command state and dialog parts-bin parity

#### should model connect callout and disconnect command outcomes

- should model connect callout and disconnect command outcomes
- Connect from an idle bridge state
   - Expected: connect.componentName equals `BridgeToggle`
   - Expected: connect.initialName equals `work laptop`
   - Expected: connect.connect is true
   - Expected: connect.onDoneMessage equals `Remote Control connecting...`
   - Expected: connect.onDoneDisplay equals `system`
   - Expected: connect.logAction equals `connect`
- Reject prerequisite errors before callout or connection
   - Expected: rejected.componentName equals `BridgeToggle`
   - Expected: rejected.initialName equals `blocked terminal`
   - Expected: rejected.onDoneMessage equals `Policy denied`
   - Expected: rejected.onDoneDisplay equals `system`
   - Expected: rejected.logAction equals `preflight_failed`
   - Expected: rejected.error equals `Policy denied`
- Show the first-run remote callout before connecting
   - Expected: callout.componentName equals `RemoteCallout`
   - Expected: callout.showRemoteCallout is true
   - Expected: callout.initialName equals `phone`
   - Expected: callout.onDoneDisplay equals `system`
   - Expected: calloutState.replBridgeInitialName equals `phone`
   - Expected: stableCalloutState.replBridgeInitialName equals `phone`
- Prompt for disconnect when full control is already active
   - Expected: dialog.componentName equals `BridgeDisconnectDialog`
   - Expected: dialog.showDisconnectDialog is true
   - Expected: dialog.connect is false
- Allow outbound-only bridge to upgrade to full control
   - Expected: callBridgeCommand("", outbound, "", false).connect is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model connect callout and disconnect command outcomes")
step("Connect from an idle bridge state")
val idle = defaultBridgeState()
val connect = callBridgeCommand("  work laptop  ", idle, "", false)
expect(connect.componentName).to_equal("BridgeToggle")
expect(connect.initialName).to_equal("work laptop")
expect(connect.connect).to_equal(true)
expect(connect.onDoneMessage).to_equal("Remote Control connecting...")
expect(connect.onDoneDisplay).to_equal("system")
expect(connect.logAction).to_equal("connect")

step("Reject prerequisite errors before callout or connection")
val rejected = callBridgeCommand("  blocked terminal  ", idle, "Policy denied", true)
expect(rejected.componentName).to_equal("BridgeToggle")
expect(rejected.initialName).to_equal("blocked terminal")
expect(rejected.showDisconnectDialog).to_be(false)
expect(rejected.showRemoteCallout).to_be(false)
expect(rejected.connect).to_be(false)
expect(rejected.onDoneMessage).to_equal("Policy denied")
expect(rejected.onDoneDisplay).to_equal("system")
expect(rejected.logAction).to_equal("preflight_failed")
expect(rejected.error).to_equal("Policy denied")

step("Show the first-run remote callout before connecting")
val callout = callBridgeCommand(" phone ", idle, "", true)
expect(callout.componentName).to_equal("RemoteCallout")
expect(callout.showRemoteCallout).to_equal(true)
expect(callout.initialName).to_equal("phone")
expect(callout.onDoneDisplay).to_equal("system")
val calloutState = calloutBridgeState(idle, "phone")
expect(calloutState.showRemoteCallout).to_be(true)
expect(calloutState.replBridgeInitialName).to_equal("phone")
expect(calloutState.replBridgeEnabled).to_be(false)
val stableCalloutState = calloutBridgeState(calloutState, "ignored")
expect(stableCalloutState.showRemoteCallout).to_be(true)
expect(stableCalloutState.replBridgeInitialName).to_equal("phone")

step("Prompt for disconnect when full control is already active")
val active = connectedBridgeState(idle, "desk")
val dialog = callBridgeCommand("", active, "", false)
expect(dialog.componentName).to_equal("BridgeDisconnectDialog")
expect(dialog.showDisconnectDialog).to_equal(true)
expect(dialog.connect).to_equal(false)

step("Allow outbound-only bridge to upgrade to full control")
val outbound = BridgeAppState(
    replBridgeConnected: false,
    replBridgeEnabled: true,
    replBridgeOutboundOnly: true,
    replBridgeExplicit: false,
    replBridgeInitialName: "",
    replBridgeSessionActive: false,
    replBridgeSessionUrl: "",
    replBridgeConnectUrl: "",
    showRemoteCallout: false,
)
expect(callBridgeCommand("", outbound, "", false).connect).to_equal(true)
```

</details>

#### should model dialog display focus actions QR filtering and disconnect state

- should model dialog display focus actions QR filtering and disconnect state
- Build a dialog model from active session state
   - Expected: model.title equals `Remote Control`
   - Expected: model.displayUrl equals `https://claude.ai/session/1`
   - Expected: model.qrButtonText equals `Show QR code`
- Check focus wrapping and accept actions
   - Expected: bridgeFocusNext(2) equals `0`
   - Expected: bridgeFocusPrevious(0) equals `2`
   - Expected: bridgeAcceptAction(0) equals `disconnect`
   - Expected: bridgeAcceptAction(1) equals `toggle_qr`
   - Expected: bridgeAcceptAction(2) equals `continue`
   - Expected: bridgeQrButtonText(true) equals `Hide QR code`
- Filter blank QR lines and clear bridge state on disconnect
   - Expected: lines.len() equals `2`
   - Expected: lines[0] equals `aa`
   - Expected: lines[1] equals `bb`
   - Expected: disconnected.replBridgeEnabled is false
   - Expected: disconnected.replBridgeExplicit is false
   - Expected: disconnected.replBridgeOutboundOnly is false
   - Expected: bridgeDisconnectMessage() equals `Remote Control disconnected.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should model dialog display focus actions QR filtering and disconnect state")
step("Build a dialog model from active session state")
val state = BridgeAppState(
    replBridgeConnected: true,
    replBridgeEnabled: true,
    replBridgeOutboundOnly: false,
    replBridgeExplicit: true,
    replBridgeInitialName: "desk",
    replBridgeSessionActive: true,
    replBridgeSessionUrl: "https://claude.ai/session/1",
    replBridgeConnectUrl: "https://claude.ai/connect/1",
    showRemoteCallout: false,
)
val model = bridgeDialogModel(state, 2, false)
expect(model.title).to_equal("Remote Control")
expect(model.displayUrl).to_equal("https://claude.ai/session/1")
expect(model.qrButtonText).to_equal("Show QR code")
expect(model.helpText).to_contain("Esc")

step("Check focus wrapping and accept actions")
expect(bridgeFocusNext(2)).to_equal(0)
expect(bridgeFocusPrevious(0)).to_equal(2)
expect(bridgeAcceptAction(0)).to_equal("disconnect")
expect(bridgeAcceptAction(1)).to_equal("toggle_qr")
expect(bridgeAcceptAction(2)).to_equal("continue")
expect(bridgeQrButtonText(true)).to_equal("Hide QR code")

step("Filter blank QR lines and clear bridge state on disconnect")
val lines = bridgeQrLines("aa\n\nbb\n")
expect(lines.len()).to_equal(2)
expect(lines[0]).to_equal("aa")
expect(lines[1]).to_equal("bb")
val disconnected = disconnectedBridgeState(state)
expect(disconnected.replBridgeEnabled).to_equal(false)
expect(disconnected.replBridgeExplicit).to_equal(false)
expect(disconnected.replBridgeOutboundOnly).to_equal(false)
expect(bridgeDisconnectMessage()).to_equal("Remote Control disconnected.")
```

</details>

### REQ-LLM-CARET-HIDDEN-008: bridge command prerequisites

#### should check prerequisite precedence and v2 assistant fallback

- should check prerequisite precedence and v2 assistant fallback
- Reject organization policy before other checks
   - Expected: checkBridgePrerequisitesModel(policy) equals `Remote Control is disabled by your organization's policy.`
- Return disabled reason before version and token checks
   - Expected: checkBridgePrerequisitesModel(disabled) equals `Bridge disabled`
- Use env-less version checks unless KAIROS assistant mode forces v1
   - Expected: bridgeUsesEnvLessPrereq(v2) is true
   - Expected: checkBridgePrerequisitesModel(v2) equals `env-less version error`
   - Expected: bridgeUsesEnvLessPrereq(assistant) is false
   - Expected: checkBridgePrerequisitesModel(assistant) equals `v1 version error`
- Require an access token after all other checks pass
   - Expected: checkBridgePrerequisitesModel(login) equals `Log in to use Remote Control.`
   - Expected: checkBridgePrerequisitesModel(prereqInput()) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should check prerequisite precedence and v2 assistant fallback")
step("Reject organization policy before other checks")
val policy = prereqInput()
policy.policyAllowed = false
policy.disabledReason = "later"
expect(checkBridgePrerequisitesModel(policy)).to_equal("Remote Control is disabled by your organization's policy.")

step("Return disabled reason before version and token checks")
val disabled = prereqInput()
disabled.disabledReason = "Bridge disabled"
disabled.envLessVersionError = "newer CLI required"
disabled.accessToken = ""
expect(checkBridgePrerequisitesModel(disabled)).to_equal("Bridge disabled")

step("Use env-less version checks unless KAIROS assistant mode forces v1")
val v2 = prereqInput()
v2.envLessVersionError = "env-less version error"
v2.bridgeMinVersionError = "v1 version error"
expect(bridgeUsesEnvLessPrereq(v2)).to_equal(true)
expect(checkBridgePrerequisitesModel(v2)).to_equal("env-less version error")

val assistant = prereqInput()
assistant.kairosFeature = true
assistant.assistantMode = true
assistant.envLessVersionError = "env-less version error"
assistant.bridgeMinVersionError = "v1 version error"
expect(bridgeUsesEnvLessPrereq(assistant)).to_equal(false)
expect(checkBridgePrerequisitesModel(assistant)).to_equal("v1 version error")

step("Require an access token after all other checks pass")
val login = prereqInput()
login.accessToken = ""
expect(checkBridgePrerequisitesModel(login)).to_equal("Log in to use Remote Control.")
expect(checkBridgePrerequisitesModel(prereqInput())).to_equal("")
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
- `REQ-LLM-CARET-HIDDEN-008`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `925d406f133d6b0090d6397b09317a6e242884d011a0ad5cc22225a87ff1fec7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `925d406f133d6b0090d6397b09317a6e242884d011a0ad5cc22225a87ff1fec7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `925d406f133d6b0090d6397b09317a6e242884d011a0ad5cc22225a87ff1fec7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/03_system/tools/llm/claude_full/commands/bridge_command_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/commands/bridge_command_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/commands/bridge_command_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/commands/bridge_command_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/commands/bridge_command_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/llm/claude_full/commands/bridge_command_spec.spl:35:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose remote-control command metadata and gate hidden state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/bridge_command_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose remote-control command metadata and gate hidden state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/bridge_command_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model connect callout and disconnect command outcomes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/bridge_command_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model connect callout and disconnect command outcomes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/bridge_command_spec.spl:116:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should model dialog display focus actions QR filtering and disconnect state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/commands/bridge_command_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should model dialog display focus actions QR filtering and disconnect state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/commands/bridge_command_spec.spl:157:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should check prerequisite precedence and v2 assistant fallback' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
