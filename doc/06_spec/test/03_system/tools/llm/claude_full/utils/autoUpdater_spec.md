# Claude Full AutoUpdater Utils

> Checks the autoUpdater class and exported result/config surface required by strict parity.

<!-- sdn-diagram:id=autoUpdater_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=autoUpdater_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

autoUpdater_spec -> std
autoUpdater_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=autoUpdater_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full AutoUpdater Utils

Checks the autoUpdater class and exported result/config surface required by strict parity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/autoUpdater_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks the autoUpdater class and exported result/config surface required by strict parity.

## Scenarios

### Claude full autoUpdater utils

#### should expose AutoUpdaterError

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = AutoUpdaterError.new("install failed")
expect(err.name).to_equal("AutoUpdaterError")
expect(err.message).to_equal("install failed")
```

</details>

#### should expose result config and status surface

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = AutoUpdaterResult.new("1.2.3", "success", ["updated"])
expect(result.version).to_equal("1.2.3")
expect(result.status).to_equal("success")
expect(result.notifications[0]).to_equal("updated")
val config = MaxVersionConfig.new("2.0.0", "3.0.0", "external blocked", "ant blocked")
expect(config.external).to_equal("2.0.0")
expect(config.antMessage).to_equal("ant blocked")
expect(isInstallStatus("success")).to_equal(true)
expect(isInstallStatus("pending")).to_equal(false)
```

</details>

#### should expose constants and source size

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(gcsBucketUrl()).to_contain("claude-code-releases")
expect(autoUpdaterSourceLinesModeled()).to_equal(561)
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
