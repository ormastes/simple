# Wine Process Session Plan Command Specification

> <details>

<!-- sdn-diagram:id=wine_process_session_plan_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wine_process_session_plan_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wine_process_session_plan_command_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wine_process_session_plan_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Process Session Plan Command Specification

## Scenarios

### Wine process session plan command

#### prints a controlled Wine hello handoff and execution result

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, code) = rt_process_run("bin/simple", ["run", "src/app/wine_process_session_plan/main.spl"])
expect(code).to_equal(0)
expect(stdout).to_contain("command=hello.exe\n")
expect(stdout).to_contain("readiness=controlled-hello-ready\n")
expect(stdout).to_contain("handoff=dry-run-ready\n")
expect(stdout).to_contain("execution=executed\n")
expect(stdout).to_contain("stdout=Hello from SimpleOS Wine\n")
expect(stderr).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/wine_process_session_plan_command_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Wine process session plan command

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
