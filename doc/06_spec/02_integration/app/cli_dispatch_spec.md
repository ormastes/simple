# Cli Dispatch Specification

> <details>

<!-- sdn-diagram:id=cli_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_dispatch_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cli Dispatch Specification

## Scenarios

### CLI Command Dispatch System

### Command Table

#### has 48 total commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = command_count()
expect count == 48
```

</details>

#### has 47 Simple implementations

1. expect simple count >= 47  # At least 47


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val simple_count = simple_impl_count()
expect simple_count >= 47  # At least 47 (test might be Rust-only)
```

</details>

#### has 98% coverage

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val coverage = coverage_percentage()
expect coverage >= 97.0  # At least 97%
```

</details>

### Command Lookup

#### finds compile command

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match find_command("compile"):
    case Some(entry):
        expect entry.name == "compile"
        expect entry.app_path == "src/app/compile/main.spl"
    case None:
        fail "compile command not found"
```

</details>

#### finds build command

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match find_command("build"):
    case Some(entry):
        expect entry.name == "build"
        expect entry.app_path == "src/app/build/main.spl"
    case None:
        fail "build command not found"
```

</details>

#### returns None for invalid command

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = find_command("invalid-command-xyz")
expect not result.?
```

</details>

### Environment Overrides

#### detects SIMPLE_COMPILE_RUST override

1. env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
env_set("SIMPLE_COMPILE_RUST", "1")
val entry = find_command("compile").unwrap()
val should_rust = entry.should_use_rust(["compile", "test.spl"])
expect should_rust
```

</details>

#### does not override when env var is unset

1. env set


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
env_set("SIMPLE_COMPILE_RUST", "")
val entry = find_command("compile").unwrap()
val should_rust = entry.should_use_rust(["compile", "test.spl"])
expect not should_rust
```

</details>

### Special Flags

#### detects --json flag for lint

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = find_command("lint").unwrap()
val should_rust = entry.should_use_rust(["lint", "--json", "file.spl"])
expect should_rust
```

</details>

#### detects --fix flag for lint

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = find_command("lint").unwrap()
val should_rust = entry.should_use_rust(["lint", "--fix", "file.spl"])
expect should_rust
```

</details>

#### does not trigger on regular args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = find_command("lint").unwrap()
val should_rust = entry.should_use_rust(["lint", "file.spl"])
expect not should_rust
```

</details>

### Simple Implementation Detection

#### reports Simple impl exists for compile

1. expect entry has simple impl


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = find_command("compile").unwrap()
expect entry.has_simple_impl()
```

</details>

#### reports Simple impl exists for build

1. expect entry has simple impl


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = find_command("build").unwrap()
expect entry.has_simple_impl()
```

</details>

#### reports no Simple impl for test

1. expect not entry has simple impl


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = find_command("test").unwrap()
expect not entry.has_simple_impl()  # Rust-only (cargo integration)
```

</details>

### Command Categories

#### has all compilation commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val commands = ["compile", "targets", "linkers", "check"]
for cmd in commands:
    val entry = find_command(cmd)
    expect entry.?
```

</details>

#### has all code quality commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val commands = ["lint", "fix", "fmt"]
for cmd in commands:
    val entry = find_command(cmd)
    expect entry.?
```

</details>

#### has all build system commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val commands = ["build", "run", "clean"]
for cmd in commands:
    val entry = find_command(cmd)
    expect entry.?
```

</details>

#### has all package management commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val commands = ["init", "install", "add", "remove", "list", "tree"]
for cmd in commands:
    val entry = find_command(cmd)
    expect entry.?
```

</details>

#### has all documentation commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val commands = ["feature-gen", "spec-gen", "todo-scan", "brief"]
for cmd in commands:
    val entry = find_command(cmd)
    expect entry.?
```

</details>

### CLI Dispatch Performance

### Dispatch Performance

#### dispatches in under 10ms overhead

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Target: <10ms dispatch overhead; generous limit (50ms) for CI variability
val start = rt_time_now_unix_micros()
val (stdout, stderr, code) = rt_process_run(find_simple_binary(), ["compile", "--help"])
val end = rt_time_now_unix_micros()
val elapsed_ms = (end - start) / 1000
expect elapsed_ms < 50
```

</details>

#### startup completes in under 25ms

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Target: <25ms startup; generous limit (100ms) for CI variability
val start = rt_time_now_unix_micros()
val (stdout, stderr, code) = rt_process_run(find_simple_binary(), ["--version"])
val end = rt_time_now_unix_micros()
val elapsed_ms = (end - start) / 1000
expect elapsed_ms < 100
```

</details>

### CLI Dispatch Robustness

### Error Handling

#### handles missing command gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = find_command("nonexistent-cmd")
expect not result.?
```

</details>

#### handles empty command name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = find_command("")
expect not result.?
```

</details>

### Edge Cases

#### handles command with no Simple impl

1. expect not entry has simple impl


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = find_command("test").unwrap()
expect not entry.has_simple_impl()
# Should fallback to Rust without crashing
```

</details>

#### handles command with empty app_path

1. expect not entry has simple impl


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = find_command("test").unwrap()
expect entry.app_path == ""
expect not entry.has_simple_impl()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/cli_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- CLI Command Dispatch System
- Command Table
- Command Lookup
- Environment Overrides
- Special Flags
- Simple Implementation Detection
- Command Categories
- CLI Dispatch Performance
- Dispatch Performance
- CLI Dispatch Robustness
- Error Handling
- Edge Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
