# Claude Full Install GitHub App Large Steps

> Checks modern SSpec parity for the main install-github-app flow and large UI steps.

<!-- sdn-diagram:id=install_github_app_large_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=install_github_app_large_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

install_github_app_large_spec -> std
install_github_app_large_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=install_github_app_large_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Install GitHub App Large Steps

Checks modern SSpec parity for the main install-github-app flow and large UI steps.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/install_github_app_large_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for the main install-github-app flow and large UI steps.

## Scenarios

### Claude full install github app large steps

#### should model API key option validation and masking

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val oauth = ApiKeyStepModel.new("oauth", "", "")
expect(oauth.canContinue).to_equal(true)
expect(oauth.submitLabel).to_equal("Sign in with Anthropic")
expect(apiKeyStepNextAction("existing-secret")).to_equal("reuse-secret")
expect(apiKeyStepCanContinue("new-key", "bad", "")).to_equal(false)
expect(apiKeyStepCanContinue("new-key", "sk-ant-1234567890", "")).to_equal(true)
expect(apiKeyStepMask("sk-ant-1234567890")).to_equal("sk-a...7890")
expect(apiKeyStepSourceLinesModeled()).to_equal(230)
```

</details>

#### should model existing secret lookup states

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val checking = CheckExistingSecretStepModel.new("", false, false)
expect(checking.secretName).to_equal("ANTHROPIC_API_KEY")
expect(checking.status).to_equal("checking")
expect(CheckExistingSecretStepModel.new("CLAUDE_KEY", true, true).status).to_equal("found")
expect(checkExistingSecretCanReuse(true, true)).to_equal(true)
expect(checkExistingSecretNextStep(true, false)).to_equal("api-key")
expect(checkExistingSecretCommand("anthropic", "claude-code", "")).to_contain("ANTHROPIC_API_KEY")
expect(checkExistingSecretStepSourceLinesModeled()).to_equal(189)
```

</details>

#### should model repository selection from URL, ssh, owner slash repo, and current repo

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(chooseRepoGhRepoArg("https://github.com/anthropic/claude-code.git")).to_equal("anthropic/claude-code")
expect(chooseRepoGhRepoArg("git@github.com:anthropic/claude-code.git")).to_equal("anthropic/claude-code")
expect(chooseRepoGhRepoArg("anthropic/claude-code")).to_equal("anthropic/claude-code")
expect(ChooseRepoStepModel.new("", true, "anthropic/current").repo).to_equal("current")
expect(chooseRepoNextStep("bad")).to_equal("choose-repo")
expect(chooseRepoStepSourceLinesModeled()).to_equal(210)
```

</details>

#### should model command setup checks and submit flow

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val command = installGitHubAppCommand()
expect(command.name).to_equal("install-github-app")
expect(command.url).to_contain("github.com/apps/claude")
expect(checkGitHubCLI(0, "gh version 2")).to_equal(true)
expect(checkGitHubCLI(127, "gh not found")).to_equal(false)
expect(checkRepositoryPermissions(0, "ok")).to_equal(true)
expect(checkRepositoryPermissions(1, "Resource not accessible")).to_equal(false)
expect(openGitHubAppInstallation("anthropic/claude-code")).to_contain("repository=anthropic/claude-code")
expect(runSetupGitHubActions("anthropic/claude-code", "", "overwrite")).to_contain("ANTHROPIC_API_KEY")
```

</details>

#### should model user handlers through creating state

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val initial = installGitHubAppCall("anthropic/current")
expect(initial.step).to_equal("check-github")
val selected = handleRepoUrlChange(initial, "anthropic/claude-code")
expect(selected.step).to_equal("check-existing-secret")
val keyed = handleOAuthSuccess(selected, "sk-ant-1234567890")
expect(keyed.apiKeyOption).to_equal("new-key")
expect(hasAnthropicKey(keyed.apiKey)).to_equal(true)
val named = handleSecretNameChange(keyed, "CLAUDE_API_KEY")
expect(named.secretName).to_equal("CLAUDE_API_KEY")
val workflow = handleWorkflowAction(named, "skip")
expect(workflow.workflowAction).to_equal("skip")
val submitted = handleSubmit(workflow)
expect(submitted.step).to_equal("creating")
expect(submitted.message).to_contain("anthropic/claude-code")
expect(installGitHubAppDismissKey("escape")).to_equal(true)
expect(installGitHubAppSourceLinesModeled()).to_equal(586)
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
