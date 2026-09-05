# T32 Terminal Power Remote Specification

> <details>

<!-- sdn-diagram:id=t32_terminal_power_remote_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_terminal_power_remote_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_terminal_power_remote_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_terminal_power_remote_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Terminal Power Remote Specification

## Scenarios

### T32 terminal power remote portable smoke

#### records terminal transport kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kinds = ["ssh", "telnet", "t32_swd", "relay"]
expect(kinds.len()).to_equal(4)
expect(kinds[0]).to_equal("ssh")
expect(kinds[2]).to_equal("t32_swd")
```

</details>

#### records power controller kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kinds = ["t32", "relay", "host"]
expect(kinds.len()).to_equal(3)
expect(kinds[1]).to_equal("relay")
```

</details>

#### records remote session kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val remote_pc_kind = 9
expect(remote_pc_kind).to_equal(9)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/hardware/t32_terminal_power_remote_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 terminal power remote portable smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
