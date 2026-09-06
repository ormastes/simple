# Claude Full Install Slack App Command

> Checks modern SSpec parity for install-slack-app descriptors.

<!-- sdn-diagram:id=install_slack_app_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=install_slack_app_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

install_slack_app_spec -> std
install_slack_app_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=install_slack_app_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Install Slack App Command

Checks modern SSpec parity for install-slack-app descriptors.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/install_slack_app_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for install-slack-app descriptors.

## Scenarios

### Claude full install slack app command

#### should expose install slack command metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(installSlackAppCommandName()).to_equal("install-slack-app")
expect(installSlackAppCommand().description).to_contain("Slack")
expect(installSlackAppCommand().url).to_contain("slack.com")
```

</details>

#### should format workspace messages

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(installSlackAppMessage("")).to_contain("installation")
expect(installSlackAppMessage("eng")).to_contain("eng")
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(installSlackAppSourceLinesModeled()).to_equal(30)
expect(installSlackAppIndexSourceLinesModeled()).to_equal(12)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
