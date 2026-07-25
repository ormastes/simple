# Claude Full Auth Utils

> Checks the auth timeout error class required by strict parity.

<!-- sdn-diagram:id=auth_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=auth_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

auth_spec -> std
auth_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=auth_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Auth Utils

Checks the auth timeout error class required by strict parity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/auth_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks the auth timeout error class required by strict parity.

## Scenarios

### Claude full auth utils

#### should expose GCP credentials timeout error

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = GcpCredentialsTimeoutError.new()
expect(err.name).to_equal("GcpCredentialsTimeoutError")
expect(err.message).to_equal("")
expect(GcpCredentialsTimeoutError.withMessage("timed out").message).to_equal("timed out")
expect(authSourceLinesModeled()).to_equal(2002)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
