# Claude Full Remote Env and Reset Limits Commands

> Checks modern SSpec parity for tiny remote env and reset limits rows.

<!-- sdn-diagram:id=remote_env_reset_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=remote_env_reset_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

remote_env_reset_spec -> std
remote_env_reset_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=remote_env_reset_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Remote Env and Reset Limits Commands

Checks modern SSpec parity for tiny remote env and reset limits rows.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/remote_env_reset_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for tiny remote env and reset limits rows.

## Scenarios

### Claude full remote env reset commands

#### should expose command names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(remoteEnvCommandName()).to_equal("remote-env")
expect(remoteEnvIndexName()).to_equal("remote-env")
expect(resetLimitsCommandName()).to_equal("reset-limits")
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(remoteEnvIndexSourceLinesModeled()).to_equal(15)
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
