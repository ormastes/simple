# Claude Full Install GitHub App Small Steps

> Checks modern SSpec parity for the small install-github-app command rows.

<!-- sdn-diagram:id=install_github_app_small_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=install_github_app_small_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

install_github_app_small_spec -> std
install_github_app_small_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=install_github_app_small_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Install GitHub App Small Steps

Checks modern SSpec parity for the small install-github-app command rows.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/install_github_app_small_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for the small install-github-app command rows.

## Scenarios

### Claude full install github app small steps

#### should expose CheckGitHub step metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(checkGitHubStepTitle()).to_equal("Check GitHub")
expect(checkGitHubStepSourceLinesModeled()).to_equal(14)
```

</details>

#### should expose install github app command index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(installGitHubAppCommandName()).to_equal("install-github-app")
expect(installGitHubAppCommandDescription()).to_contain("GitHub")
expect(installGitHubAppIndexSourceLinesModeled()).to_equal(13)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
