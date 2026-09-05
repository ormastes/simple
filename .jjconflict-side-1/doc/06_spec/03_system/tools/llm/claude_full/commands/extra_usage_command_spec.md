# Claude Full Extra Usage Command

> Focused parity for `tmp/claude/claude-code-main/src/commands/extra-usage`.

<!-- sdn-diagram:id=extra_usage_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=extra_usage_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

extra_usage_command_spec -> std
extra_usage_command_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=extra_usage_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Extra Usage Command

Focused parity for `tmp/claude/claude-code-main/src/commands/extra-usage`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/extra_usage_command_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Focused parity for `tmp/claude/claude-code-main/src/commands/extra-usage`.

## Scenarios

### Claude full extra-usage command

#### keeps the owned Simple mirrors at the upstream line floors

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val core = extraUsageSource("src/app/llm_caret/claude_full/commands/extra-usage/extra-usage-core.spl")
val noninteractive = extraUsageSource("src/app/llm_caret/claude_full/commands/extra-usage/extra-usage-noninteractive.spl")
val interactive = extraUsageSource("src/app/llm_caret/claude_full/commands/extra-usage/extra-usage.spl")
val index = extraUsageSource("src/app/llm_caret/claude_full/commands/extra-usage/index.spl")
expect(countLines(core)).to_be_greater_than(117)
expect(countLines(noninteractive)).to_be_greater_than(15)
expect(countLines(interactive)).to_be_greater_than(15)
expect(countLines(index)).to_be_greater_than(30)
expect(extraUsageCoreSourceLinesModeled()).to_equal(118)
expect(extraUsageNoninteractiveSourceLinesModeled()).to_equal(16)
expect(extraUsageInteractiveSourceLinesModeled()).to_equal(16)
expect(extraUsageIndexSourceLinesModeled()).to_equal(31)
```

</details>

#### models admin request branches for team users without billing access

- var state = ExtraUsageState teamMemberWithoutBilling
- var result = runExtraUsage
   - Expected: result.value equals `Request sent to your admin to enable extra usage.`
   - Expected: result.adminRequestCreated is true
   - Expected: result.requestAction equals `limit_increase`
   - Expected: result.visitedSaved is true
   - Expected: result.cacheInvalidated is true
- result = runExtraUsage
   - Expected: result.value equals `Request sent to your admin to increase extra usage.`
- result = runExtraUsage
   - Expected: result.value equals `Your organization already has unlimited extra usage. No request needed.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = ExtraUsageState.teamMemberWithoutBilling()
var result = runExtraUsage(state)
expect(result.value).to_equal("Request sent to your admin to enable extra usage.")
expect(result.adminRequestCreated).to_equal(true)
expect(result.requestAction).to_equal("limit_increase")
expect(result.visitedSaved).to_equal(true)
expect(result.cacheInvalidated).to_equal(true)

state.extraUsageEnabled = true
result = runExtraUsage(state)
expect(result.value).to_equal("Request sent to your admin to increase extra usage.")

state.monthlyLimitUnlimited = true
result = runExtraUsage(state)
expect(result.value).to_equal("Your organization already has unlimited extra usage. No request needed.")
```

</details>

#### models admin denial, duplicate request, and fallback messages

- var state = ExtraUsageState teamMemberWithoutBilling
   - Expected: runExtraUsage(state).value equals `Please contact your admin to manage extra usage settings.`
- state = ExtraUsageState teamMemberWithoutBilling
   - Expected: runExtraUsage(state).value equals `You have already submitted a request for extra usage to your admin.`
- state = ExtraUsageState teamMemberWithoutBilling
   - Expected: runExtraUsage(state).value equals `Please contact your admin to manage extra usage settings.`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = ExtraUsageState.teamMemberWithoutBilling()
state.eligibilityAllowed = false
expect(runExtraUsage(state).value).to_equal("Please contact your admin to manage extra usage settings.")

state = ExtraUsageState.teamMemberWithoutBilling()
state.pendingRequestCount = 1
expect(runExtraUsage(state).value).to_equal("You have already submitted a request for extra usage to your admin.")

state = ExtraUsageState.teamMemberWithoutBilling()
state.createRequestFails = true
expect(runExtraUsage(state).value).to_equal("Please contact your admin to manage extra usage settings.")
```

</details>

#### models browser URLs and wrapper output

- var state = ExtraUsageState individualWithBilling
- var result = runExtraUsage
   - Expected: result.typeName equals `browser-opened`
   - Expected: result.url equals `https://claude.ai/settings/usage`
   - Expected: callExtraUsageInteractive(state).rendersLogin is true
- result = runExtraUsage
   - Expected: result.url equals `https://claude.ai/admin-settings/usage`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = ExtraUsageState.individualWithBilling()
var result = runExtraUsage(state)
expect(result.typeName).to_equal("browser-opened")
expect(result.url).to_equal("https://claude.ai/settings/usage")
expect(callExtraUsageNoninteractive(state).value).to_contain("Browser opened")
expect(callExtraUsageInteractive(state).rendersLogin).to_equal(true)
expect(callExtraUsageInteractive(state).startingMessage).to_contain("Starting new login")

state.subscriptionType = "enterprise"
result = runExtraUsage(state)
expect(result.url).to_equal("https://claude.ai/admin-settings/usage")

state.browserOpenFails = true
expect(runExtraUsage(state).value).to_contain("Failed to open browser")
```

</details>

#### models index enablement and hidden state

- var state = ExtraUsageState individualWithBilling
   - Expected: extraUsageCommand(state).typeName equals `local-jsx`
   - Expected: extraUsageCommand(state).enabled is true
   - Expected: extraUsageNonInteractiveCommand(state).enabled is false
   - Expected: extraUsageNonInteractiveCommand(state).isHidden is true
   - Expected: extraUsageCommandName() equals `extra-usage`
   - Expected: extraUsageCommand(state).enabled is false
   - Expected: extraUsageNonInteractiveCommand(state).enabled is true
   - Expected: extraUsageNonInteractiveCommand(state).isHidden is false
   - Expected: extraUsageNonInteractiveCommand(state).enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = ExtraUsageState.individualWithBilling()
expect(extraUsageCommand(state).typeName).to_equal("local-jsx")
expect(extraUsageCommand(state).enabled).to_equal(true)
expect(extraUsageNonInteractiveCommand(state).enabled).to_equal(false)
expect(extraUsageNonInteractiveCommand(state).isHidden).to_equal(true)
expect(extraUsageCommandName()).to_equal("extra-usage")

state.nonInteractive = true
expect(extraUsageCommand(state).enabled).to_equal(false)
expect(extraUsageNonInteractiveCommand(state).enabled).to_equal(true)
expect(extraUsageNonInteractiveCommand(state).isHidden).to_equal(false)

state.disableCommand = true
expect(extraUsageNonInteractiveCommand(state).enabled).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
