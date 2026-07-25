# Claude Full Install GitHub App Finish Steps

> Checks modern SSpec parity for the remaining install-github-app finish steps.

<!-- sdn-diagram:id=install_github_app_finish_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=install_github_app_finish_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

install_github_app_finish_spec -> std
install_github_app_finish_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=install_github_app_finish_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Install GitHub App Finish Steps

Checks modern SSpec parity for the remaining install-github-app finish steps.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/install_github_app_finish_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for the remaining install-github-app finish steps.

## Scenarios

### Claude full install github app finish steps

#### should model oauth flow status and key actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flow = OAuthFlowStepModel.new("waiting", "https://console.anthropic.com/oauth", "ABCD-EFGH", "")
expect(flow.status).to_equal("waiting")
expect(oauthFlowStepTitle()).to_equal("Sign in with Anthropic")
expect(oauthFlowStepInstructions(flow.deviceUrl, flow.userCode)).to_contain("ABCD-EFGH")
expect(oauthFlowStepStatusLine("success")).to_equal("Authentication complete")
expect(oauthFlowStepCanCancel("waiting")).to_equal(true)
expect(oauthFlowStepCanRetry("error")).to_equal(true)
expect(oauthFlowStepNextAction("success", "enter")).to_equal("continue")
expect(oauthFlowStepErrorLine("denied")).to_contain("denied")
expect(oauthFlowStepSourceLinesModeled()).to_equal(275)
```

</details>

#### should model github actions setup planning

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = GitHubActionsSetupPlan.new("https://github.com/anthropic/claude-code.git", "", "overwrite")
expect(plan.repo).to_equal("anthropic/claude-code")
expect(plan.secretName).to_equal("ANTHROPIC_API_KEY")
expect(plan.workflowPath).to_equal(".github/workflows/claude.yml")
expect(setupGitHubActionsShouldWriteWorkflow("skip")).to_equal(false)
expect(setupGitHubActionsSecretCommand("anthropic/claude-code", "CLAUDE_API_KEY")).to_contain("CLAUDE_API_KEY")
expect(setupGitHubActionsWorkflowYaml("ANTHROPIC_API_KEY")).to_contain("anthropics/claude-code-action@beta")
expect(setupGitHubActionsSummary("git@github.com:anthropic/claude-code.git", "", "bad")).to_contain("using create")
expect(setupGitHubActionsSourceLinesModeled()).to_equal(325)
```

</details>

#### should model success copy

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(successStepTitle()).to_equal("Claude GitHub App installed")
expect(successStepStatus()).to_equal("success")
expect(successStepRepoLine("anthropic/claude-code")).to_equal("Repository: anthropic/claude-code")
expect(successStepSecretLine("")).to_equal("Secret configured: ANTHROPIC_API_KEY")
expect(successStepWorkflowLine("skip")).to_equal("Workflow file was not changed")
expect(successStepSummary("anthropic/claude-code", "CLAUDE_API_KEY", "create")).to_contain(".github/workflows/claude.yml")
expect(successStepDonePrompt()).to_equal("Press Enter to finish")
expect(successStepSourceLinesModeled()).to_equal(95)
```

</details>

#### should model warning copy

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(warningsStepTitle()).to_equal("Warnings")
expect(warningsStepStatus()).to_equal("warning")
expect(warningsStepFormat(0)).to_equal("No warnings")
expect(warningsStepFormat(1)).to_equal("1 warning found")
expect(warningsStepFormat(2)).to_equal("2 warnings found")
expect(warningsStepPermissionWarning()).to_contain("permissions")
expect(warningsStepSecretWarning("ANTHROPIC_API_KEY")).to_contain("ANTHROPIC_API_KEY")
expect(warningsStepWorkflowWarning(".github/workflows/claude.yml")).to_contain(".github/workflows/claude.yml")
expect(warningsStepSourceLinesModeled()).to_equal(72)
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
