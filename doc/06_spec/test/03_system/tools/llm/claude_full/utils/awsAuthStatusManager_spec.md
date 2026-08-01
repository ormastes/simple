# Claude Full AwsAuthStatusManager

> Checks cloud auth refresh status state transitions.

<!-- sdn-diagram:id=awsAuthStatusManager_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=awsAuthStatusManager_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

awsAuthStatusManager_spec -> std
awsAuthStatusManager_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=awsAuthStatusManager_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full AwsAuthStatusManager

Checks cloud auth refresh status state transitions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/awsAuthStatusManager_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks cloud auth refresh status state transitions.

## Scenarios

### Claude full AwsAuthStatusManager

#### should start authentication and emit status changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manager = AwsAuthStatusManager.new().startAuthentication()
val status = manager.getStatus()
expect(status.isAuthenticating).to_equal(true)
expect(status.output.len()).to_equal(0)
expect(manager.changeCount).to_equal(1)
```

</details>

#### should retain output and error on failed authentication

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manager = AwsAuthStatusManager.new().startAuthentication().addOutput("checking credentials").setError("denied").endAuthentication(false)
val status = manager.getStatus()
expect(status.isAuthenticating).to_equal(false)
expect(status.output[0]).to_equal("checking credentials")
expect(status.error).to_equal("denied")
expect(manager.changeCount).to_equal(4)
```

</details>

#### should clear status on success and reset for tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val manager = AwsAuthStatusManager.new().startAuthentication().addOutput("ok").endAuthentication(true)
expect(manager.getStatus().output.len()).to_equal(0)
expect(manager.getStatus().error).to_equal("")
expect(AwsAuthStatusManager.reset().changeCount).to_equal(0)
expect(awsAuthStatusManagerSourceLinesModeled()).to_equal(81)
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
