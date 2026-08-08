# Llm Runtime Control Command Specification

> <details>

<!-- sdn-diagram:id=llm_runtime_control_command_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llm_runtime_control_command_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llm_runtime_control_command_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llm_runtime_control_command_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Llm Runtime Control Command Specification

## Scenarios

### LLM runtime control CLI command registration

#### registers llm-runtime-control in command table

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = source("src/app/cli/dispatch/table.spl")

expect(table).to_contain("name: \"llm-runtime-control\"")
expect(table).to_contain("app_path: \"src/app/llm_runtime/control_cli.spl\"")
```

</details>

#### registers llm-runtime-control in the Rust driver app table

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val driver = source("src/compiler_rust/driver/src/main.rs")

expect(driver).to_contain("name: \"llm-runtime-control\"")
expect(driver).to_contain("app_path: \"src/app/llm_runtime/control_cli.spl\"")
expect(driver).to_contain("app_relative_path != \"src/app/llm_runtime/control_cli.spl\"")
expect(driver).to_contain("if app_relative_path == \"src/app/llm_runtime/control_cli.spl\"")
```

</details>

#### keeps direct dispatcher branch routed to runtime owner

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dispatcher = source("src/app/cli/main_part2.spl")

expect(dispatcher).to_contain("elif str_eq(first, \"llm-runtime-control\"):")
expect(dispatcher).to_contain("cli_run_file(\"src/app/llm_runtime/control_cli.spl\", filtered_args")
```

</details>

#### shows operator help for runtime control

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val help = source("src/app/cli/cli_helpers.spl")

expect(help).to_contain("simple llm-runtime-control --action preflight")
expect(help).to_contain("--base-model <model> --endpoint <url>")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/cli/llm_runtime_control_command_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LLM runtime control CLI command registration

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
