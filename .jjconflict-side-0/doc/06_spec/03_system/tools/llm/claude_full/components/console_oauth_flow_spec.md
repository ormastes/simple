# Claude Full Console OAuth Flow

> ConsoleOAuthFlow models the terminal sign-in state used by Claude Full when a provider asks the user to open a browser URL and enter or copy a one-time code. The executable spec covers provider defaults, auth URL and code normalization, step labels, terminal status copy, success/error behavior, copy/open actions, and the source helper used for parity accounting.

<!-- sdn-diagram:id=console_oauth_flow_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=console_oauth_flow_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

console_oauth_flow_spec -> std
console_oauth_flow_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=console_oauth_flow_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Console OAuth Flow

ConsoleOAuthFlow models the terminal sign-in state used by Claude Full when a provider asks the user to open a browser URL and enter or copy a one-time code. The executable spec covers provider defaults, auth URL and code normalization, step labels, terminal status copy, success/error behavior, copy/open actions, and the source helper used for parity accounting.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/tools/llm/claude_full/components/console_oauth_flow_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

ConsoleOAuthFlow models the terminal sign-in state used by Claude Full when a
provider asks the user to open a browser URL and enter or copy a one-time code.
The executable spec covers provider defaults, auth URL and code normalization,
step labels, terminal status copy, success/error behavior, copy/open actions,
and the source helper used for parity accounting.

## Examples

Create the default Anthropic provider, build a waiting state with a browser URL
and code, render the instruction text, then use the copy/open helpers to expose
side-effect requests without performing the side effects inside the model.

**Requirements:** N/A
**Plan:** N/A
**Design:** N/A
**Research:** N/A

## Scenarios

### Claude full console oauth flow

#### should model provider defaults and source helper

- Create provider
   - Expected: provider.id equals `anthropic`
   - Expected: provider.name equals `Anthropic`
   - Expected: provider.authUrl equals `https://example.test/auth`
   - Expected: provider.codeLabel equals `code`
   - Expected: consoleOAuthSourceHelper(provider) equals `ConsoleOAuthFlow:anthropic`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create provider")
val provider = ConsoleOAuthProvider.new("", "", " https://example.test/auth ", "", "")
expect(provider.id).to_equal("anthropic")
expect(provider.name).to_equal("Anthropic")
expect(provider.authUrl).to_equal("https://example.test/auth")
expect(provider.codeLabel).to_equal("code")
expect(consoleOAuthSourceHelper(provider)).to_equal("ConsoleOAuthFlow:anthropic")
```

</details>

#### should model url code state and actions

- Create waiting flow
   - Expected: state.status equals `waiting`
   - Expected: state.authUrl equals `https://console.anthropic.com/oauth/authorize`
   - Expected: state.userCode equals `ABCD-EFGH`
   - Expected: consoleOAuthCopyAction(state) equals `copy-code:ABCD-EFGH`
   - Expected: consoleOAuthCanCopy(state) is true
   - Expected: consoleOAuthCanOpen(state) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create waiting flow")
val provider = consoleOAuthAnthropicProvider()
val state = ConsoleOAuthFlowState.new(provider, "waiting", "", " ABCD-EFGH ", false, false, "")
expect(state.status).to_equal("waiting")
expect(state.authUrl).to_equal("https://console.anthropic.com/oauth/authorize")
expect(state.userCode).to_equal("ABCD-EFGH")
expect(consoleOAuthInstruction(state)).to_contain("ABCD-EFGH")
expect(consoleOAuthCopyAction(state)).to_equal("copy-code:ABCD-EFGH")
expect(consoleOAuthOpenAction(state)).to_contain("open-url:https://")
expect(consoleOAuthCanCopy(state)).to_equal(true)
expect(consoleOAuthCanOpen(state)).to_equal(true)
```

</details>

#### should model step labels and success error statuses

- Read labels
   - Expected: consoleOAuthStepLabel("idle") equals `Ready to sign in`
   - Expected: consoleOAuthStepLabel("opening-browser") equals `Opening browser`
   - Expected: consoleOAuthStepLabel("copied-code") equals `Code copied`
   - Expected: consoleOAuthStatusLine(success) equals `Anthropic authentication complete`
   - Expected: consoleOAuthPrimaryAction("success") equals `continue`
   - Expected: consoleOAuthPrimaryAction("error") equals `retry`
   - Expected: consoleOAuthNormalizeStatus("bogus") equals `idle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Read labels")
val provider = consoleOAuthAnthropicProvider()
val success = ConsoleOAuthFlowState.new(provider, "success", "", "DONE", true, true, "")
val failure = ConsoleOAuthFlowState.new(provider, "error", "", "", false, false, "access denied")
expect(consoleOAuthStepLabel("idle")).to_equal("Ready to sign in")
expect(consoleOAuthStepLabel("opening-browser")).to_equal("Opening browser")
expect(consoleOAuthStepLabel("copied-code")).to_equal("Code copied")
expect(consoleOAuthStatusLine(success)).to_equal("Anthropic authentication complete")
expect(consoleOAuthStatusLine(failure)).to_contain("access denied")
expect(consoleOAuthPrimaryAction("success")).to_equal("continue")
expect(consoleOAuthPrimaryAction("error")).to_equal("retry")
expect(consoleOAuthNormalizeStatus("bogus")).to_equal("idle")
```

</details>

#### should model copy open mutations and source floor

- Apply actions
   - Expected: state.copyCode().copied is true
   - Expected: state.openUrl().opened is true
   - Expected: state.withStatus("success", "ignored").status equals `success`
   - Expected: consoleOAuthSourceLinesModeled() equals `630`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Apply actions")
val provider = consoleOAuthAnthropicProvider()
val state = ConsoleOAuthFlowState.new(provider, "waiting", "https://auth.test", "CODE", false, false, "")
expect(state.copyCode().copied).to_equal(true)
expect(state.openUrl().opened).to_equal(true)
expect(state.withStatus("success", "ignored").status).to_equal("success")
expect(consoleOAuthRenderSummary(state)).to_contain("Sign in with Anthropic")
expect(consoleOAuthSourceLinesModeled()).to_equal(630)
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
