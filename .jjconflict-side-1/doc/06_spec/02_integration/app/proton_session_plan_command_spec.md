# Proton Session Plan Command Specification

> <details>

<!-- sdn-diagram:id=proton_session_plan_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=proton_session_plan_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

proton_session_plan_command_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=proton_session_plan_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Proton Session Plan Command Specification

## Scenarios

### Proton session plan command

#### prints a non-Wine Proton launch-session plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = rt_process_run("bin/simple", ["run", "src/app/proton_session_plan/main.spl"])
expect(code).to_equal(0)
expect(stdout).to_contain("app_id=480\n")
expect(stdout).to_contain("prefix=steamapps/compatdata/480/pfx\n")
expect(stdout).to_contain("command=hl2.exe -novid\n")
expect(stdout).to_contain("status=dry-run-ready\n")
expect(stdout).to_contain("exec_env=mdsoc-ready\n")
expect(stdout).to_contain("container=pressure-vessel")
expect(stdout).to_contain("steam-runtime")
expect(stdout).to_contain("pressure-vessel-container")
expect(stdout).to_contain("dxvk")
expect(stdout).to_contain("vkd3d-proton")
expect(stderr).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/proton_session_plan_command_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Proton session plan command

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
