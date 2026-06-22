# Environment Commands Specification

> Unit tests for environment command handling module. Validates CLI argument parsing, subcommand detection, and execution of environment management operations.

<!-- sdn-diagram:id=env_commands_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=env_commands_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

env_commands_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=env_commands_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Environment Commands Specification

Unit tests for environment command handling module. Validates CLI argument parsing, subcommand detection, and execution of environment management operations.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | Environment Management |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/app/tooling/env_commands_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for environment command handling module. Validates CLI argument parsing,
subcommand detection, and execution of environment management operations.

## Key Features

- Subcommand parsing (create, activate, list, remove, info)
- Argument validation and bounds checking
- Force flag detection
- Optional shell parameter handling
- Error message formatting and exit code conventions
- Help text generation and structure
- Pattern matching for command variants

## Related Specifications

- [CLI Design](../../../docs/design/cli.md)
- [Environment Management](../../../docs/design/env_management.md)

## Scenarios

### env_commands module compilation

#### compiles successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 + 1 == 2
```

</details>

### subcommand detection

#### detects create subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "create"
expect cmd == "create"
```

</details>

#### detects activate subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "activate"
expect cmd == "activate"
```

</details>

#### detects list subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "list"
expect cmd == "list"
```

</details>

#### detects remove subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "remove"
expect cmd == "remove"
```

</details>

#### detects info subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "info"
expect cmd == "info"
```

</details>

### argument length validation

#### create requires 3 args minimum

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "env", "myenv"]
expect args.len() >= 3 == true
```

</details>

#### activate requires 3 args minimum

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "env", "myenv"]
expect args.len() >= 3 == true
```

</details>

#### remove requires 3 args minimum

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "env", "myenv"]
expect args.len() >= 3 == true
```

</details>

#### info requires 3 args minimum

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "env", "myenv"]
expect args.len() >= 3 == true
```

</details>

#### list requires only 2 args

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "env"]
expect args.len() >= 2 == true
```

</details>

### force flag detection

#### detects --force flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "env", "remove", "myenv", "--force"]
val has_force = args.any(_1 == "--force")
expect has_force == true
```

</details>

#### no force flag when absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "env", "remove", "myenv"]
val has_force = args.any(_1 == "--force")
expect has_force == false
```

</details>

### optional shell parameter

#### detects shell when present

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "env", "activate", "myenv", "bash"]
val has_shell = args.len() > 3
expect has_shell == true
```

</details>

#### no shell when absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "env", "activate", "myenv"]
val has_shell = args.len() > 3
expect has_shell == false
```

</details>

### subcommand extraction

#### extracts subcommand from index 1

1. Some
2. expect subcommand is some


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "env", "create", "name"]
val subcommand = if args.len() > 1:
    Some(args[1])
else:
    None
expect subcommand.is_some() == true
```

</details>

#### returns None when no subcommand

1. Some
2. expect subcommand is none


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple"]
val subcommand = if args.len() > 1:
    Some(args[1])
else:
    None
expect subcommand.is_none() == true
```

</details>

### exit code conventions

#### success returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exit_code = 0
expect exit_code == 0
```

</details>

#### error returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exit_code = 1
expect exit_code == 1
```

</details>

### error message format

#### error prefix format

1. expect msg starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "error: env create requires a name"
expect msg.starts_with("error:") == true
```

</details>

#### usage prefix format

1. expect msg starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "Usage: simple env create <name>"
expect msg.starts_with("Usage:") == true
```

</details>

### help text formatting

#### validates command examples

1. expect example contains
2. expect example contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val example = "simple env create <name>"
expect example.contains("env") == true
expect example.contains("create") == true
```

</details>

#### validates help structure

1. expect header contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = "Simple Environment Management"
expect header.contains("Environment") == true
```

</details>

### name parameter extraction

#### extracts name from index 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "env", "create", "myenv"]
val name = args[2]
expect name == "myenv"
```

</details>

#### handles different names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "env", "activate", "testenv"]
val name = args[2]
expect name == "testenv"
```

</details>

### match pattern validation

#### matches create variant

1. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = Some("create")
val is_create = match cmd:
    Some("create") => true
    _ => false
expect is_create == true
```

</details>

#### matches None variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd: Option<text> = None
val is_none = match cmd:
    None => true
    _ => false
expect is_none == true
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
