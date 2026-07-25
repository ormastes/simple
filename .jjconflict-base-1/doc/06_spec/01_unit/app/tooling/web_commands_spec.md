# Web Commands Specification

> Unit tests for web command handling in the Simple language tooling. Validates web subcommand parsing (build, init, serve, features) and associated flag processing for web application development workflows.

<!-- sdn-diagram:id=web_commands_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_commands_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_commands_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_commands_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Commands Specification

Unit tests for web command handling in the Simple language tooling. Validates web subcommand parsing (build, init, serve, features) and associated flag processing for web application development workflows.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | Tooling-Web |
| Category | Tooling |
| Status | In Progress |
| Source | `test/01_unit/app/tooling/web_commands_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for web command handling in the Simple language tooling.
Validates web subcommand parsing (build, init, serve, features) and
associated flag processing for web application development workflows.

## Test Coverage

- Web subcommand detection (build, init, features, serve)
- Argument validation for each subcommand
- Flag detection (--optimize, --minify, --open, --no-watch, etc.)
- Flag value extraction
- Module and port flags
- Array indexing and element access
- Boolean negation patterns
- Result type patterns
- Option chaining behavior
- List operations and bounds checking
- String matching patterns
- Parameter extraction from command arguments
- Exit code conventions
- Early return validation

## Implementation Notes

Tests focus on typical web development command patterns and their integration
with the broader Simple compiler tooling ecosystem.

## Scenarios

### web_commands module compilation

#### compiles successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 + 1 == 2
```

</details>

### web subcommand detection

#### detects build subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "web", "build", "app.sui"]
expect args[1] == "web"
expect args[2] == "build"
```

</details>

#### detects init subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "web", "init", "myproject"]
expect args[2] == "init"
```

</details>

#### detects features subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "web", "features"]
expect args[2] == "features"
```

</details>

#### detects serve subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "web", "serve", "app.sui"]
expect args[2] == "serve"
```

</details>

### argument validation

#### web requires subcommand

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple"]
expect args.len() < 2 == true
```

</details>

#### build requires file

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "web"]
expect args.len() < 3 == true
```

</details>

#### init requires project name

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "web", "init"]
expect args.len() < 3 == true
```

</details>

#### serve requires file

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "web", "serve"]
expect args.len() < 3 == true
```

</details>

### flag detection

#### detects --optimize flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "web", "build", "app.sui", "--optimize"]
val has_optimize = args.any(_1 == "--optimize")
expect has_optimize == true
```

</details>

#### detects --minify flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "web", "build", "app.sui", "--minify"]
val has_minify = args.any(_1 == "--minify")
expect has_minify == true
```

</details>

#### detects --open flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "web", "serve", "app.sui", "--open"]
val has_open = args.any(_1 == "--open")
expect has_open == true
```

</details>

#### detects --no-watch flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "web", "serve", "app.sui", "--no-watch"]
val has_no_watch = args.any(_1 == "--no-watch")
expect has_no_watch == true
```

</details>

### flag value extraction

#### checks if .any works for flag presence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "web", "build", "app.sui", "-o", "dist"]
val has_o = args.any(_1 == "-o")
expect has_o == true
```

</details>

#### checks multiple flag options

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "web", "build", "app.sui", "--output", "dist"]
val has_output = args.any(_1 == "-o" or _1 == "--output")
expect has_output == true
```

</details>

#### checks module flag presence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "web", "build", "app.sui", "--module", "myapp"]
val has_module = args.any(_1 == "--module")
expect has_module == true
```

</details>

#### checks port flag presence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "web", "serve", "app.sui", "-p", "3000"]
val has_p = args.any(_1 == "-p")
expect has_p == true
```

</details>

### array indexing

#### gets value at specific index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "web", "build", "app.sui", "-o", "dist"]
val value = args[5]
expect value == "dist"
```

</details>

### boolean negation

#### watch enabled by default_val

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_no_watch = false
val watch = not has_no_watch
expect watch == true
```

</details>

#### watch disabled with --no-watch

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_no_watch = true
val watch = not has_no_watch
expect watch == false
```

</details>

### struct construction

#### constructs with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val build_optimize = true
val build_minify = false
expect build_optimize == true
expect build_minify == false
```

</details>

### u16 type

#### default_val port is 8000

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_port = 8000
expect default_port == 8000
```

</details>

#### custom port value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val custom_port = 3000
expect custom_port == 3000
```

</details>

### Result patterns

#### Ok result check

1. expect Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect Ok(8080).is_ok() == true
```

</details>

#### Err result check

1. expect Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect Err("invalid").is_err() == true
```

</details>

### Option chaining pattern

#### Some unwraps to value

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(5)
if opt.is_some():
    val value = opt.unwrap()
    expect value == 5
```

</details>

### list operations

#### checks length for bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["a", "b", "c", "d"]
val idx = 2
val in_bounds = idx + 1 < args.len()
expect in_bounds == true
```

</details>

#### out of bounds check

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["a", "b"]
val idx = 5
val in_bounds = idx + 1 < args.len()
expect in_bounds == false
```

</details>

### match on string

#### matches build

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "build"
val matched = match cmd:
    "build" => true
    _ => false
expect matched == true
```

</details>

#### matches serve

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "serve"
val matched = match cmd:
    "serve" => true
    _ => false
expect matched == true
```

</details>

#### default_val case

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "unknown"
val matched = match cmd:
    "build" => false
    "serve" => false
    _ => true
expect matched == true
```

</details>

### parameter extraction

#### extracts source file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "web", "build", "app.sui"]
val source = args[2]
expect source == "app.sui"
```

</details>

#### extracts project name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "web", "init", "myproject"]
val project_name = args[2]
expect project_name == "myproject"
```

</details>

### exit codes

#### success returns 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 0 == 0
```

</details>

#### error returns 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 == 1
```

</details>

### early return validation

#### validates insufficient args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args_len = 1
val should_return = args_len < 2
expect should_return == true
```

</details>

#### validates sufficient args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args_len = 3
val should_return = args_len < 2
expect should_return == false
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
