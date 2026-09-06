# Claude Full Install GitHub App Medium Steps

> Checks modern SSpec parity for the medium install-github-app command rows.

<!-- sdn-diagram:id=install_github_app_medium_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=install_github_app_medium_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

install_github_app_medium_spec -> std
install_github_app_medium_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=install_github_app_medium_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Install GitHub App Medium Steps

Checks modern SSpec parity for the medium install-github-app command rows.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/install_github_app_medium_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for the medium install-github-app command rows.

## Scenarios

### Claude full install github app medium steps

#### should expose creating step workflow progress

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(creatingStepTitle()).to_equal("Create GitHub Actions workflow")
expect(creatingStepCommandTitle()).to_equal("Install GitHub App")
expect(creatingStepProgressLabel("repo", false)).to_equal("Getting repository information")
expect(creatingStepProgressLabel("secret", true)).to_equal("Using existing API key secret")
expect(creatingStepProgressLabel("file", false)).to_equal("Creating workflow file")
expect(creatingStepWorkflowPrompt(true)).to_equal("Skip workflow update (configure secrets only)")
expect(creatingStepSourceLinesModeled()).to_equal(64)
```

</details>

#### should expose error step recovery copy

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(errorStepTitle()).to_equal("Install GitHub App")
expect(errorStepStatus()).to_equal("error")
expect(errorStepErrorLine("boom")).to_equal("Error: boom")
expect(errorStepReasonLine("missing gh")).to_equal("Reason: missing gh")
expect(errorStepSummary("boom", "missing gh", "Run gh auth login")).to_contain("How to fix:")
expect(errorStepManualHelpLine()).to_equal("For manual setup instructions, see:")
expect(errorStepExitPrompt()).to_equal("Press any key to exit")
expect(errorStepSourceLinesModeled()).to_equal(84)
```

</details>

#### should expose existing workflow choices

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(existingWorkflowStepTitle()).to_equal("Existing Workflow Found")
expect(existingWorkflowStepRepoLine("anthropics/claude-cli")).to_equal("Repository: anthropics/claude-cli")
expect(existingWorkflowStepPath()).to_equal(".github/workflows/claude.yml")
expect(existingWorkflowStepUpdateAction()).to_equal("Update workflow file with latest version")
expect(existingWorkflowStepSkipAction()).to_equal("Skip workflow update (configure secrets only)")
expect(existingWorkflowStepExitAction()).to_equal("Exit without making changes")
expect(existingWorkflowStepDefaultAction("")).to_equal("update")
expect(existingWorkflowStepTemplateUrl()).to_contain("claude-code-action")
expect(existingWorkflowStepSourceLinesModeled()).to_equal(102)
```

</details>

#### should expose install app browser instructions

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(installAppStepTitle()).to_equal("Install the Claude GitHub App")
expect(installAppStepCommandTitle()).to_equal("Install GitHub App")
expect(installAppStepConfirmKey()).to_equal("confirm:yes")
expect(installAppStepUrl()).to_equal("https://github.com/apps/claude")
expect(installAppStepRepositoryLine("anthropics/claude-cli")).to_contain("anthropics/claude-cli")
expect(installAppStepRepositoryWarning()).to_contain("specific repository")
expect(installAppStepContinuePrompt()).to_equal("Press Enter once you've installed the app")
expect(installAppStepTroubleLine()).to_equal("Having trouble? See manual setup instructions at:")
expect(installAppStepSourceLinesModeled()).to_equal(93)
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
