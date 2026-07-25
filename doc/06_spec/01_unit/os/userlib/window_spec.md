# Window Client Identity Specification

> Verifies that window identity defaults to the launched binary path when

<!-- sdn-diagram:id=window_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=window_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

window_spec -> std
window_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=window_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Client Identity Specification

Verifies that window identity defaults to the launched binary path when

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/userlib/window_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies that window identity defaults to the launched binary path when
applications do not explicitly provide an app_id.

## Scenarios

### Window client identity

#### uses argv[0] as the default app identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app_id = window_default_app_identity_from_args(["/sys/apps/hello_world"])
expect(app_id).to_equal("/sys/apps/hello_world")
```

</details>

#### returns empty identity when argv is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(window_default_app_identity_from_args([])).to_equal("")
expect(window_default_app_identity_from_args([""])).to_equal("")
```

</details>

### WindowClient primary window selection

#### starts without a primary window

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val client = WindowClient.new()
expect(client.get_window_id()).to_equal(0)
```

</details>

#### updates the primary window used by convenience helpers

1. var client = WindowClient new
2. client set primary window
   - Expected: client.get_window_id() equals `42`
3. client set primary window
   - Expected: client.get_window_id() equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var client = WindowClient.new()
client.set_primary_window(42)
expect(client.get_window_id()).to_equal(42)
client.set_primary_window(9)
expect(client.get_window_id()).to_equal(9)
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
