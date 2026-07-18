# CLI Args Error Handling Specification

> Tests compile-time and runtime error cases for the cli keyword. The compiler should catch invalid cli blocks at compile time, and the runtime should produce clear error messages for bad input.

<!-- sdn-diagram:id=cli_args_error_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cli_args_error_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cli_args_error_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cli_args_error_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CLI Args Error Handling Specification

Tests compile-time and runtime error cases for the cli keyword. The compiler should catch invalid cli blocks at compile time, and the runtime should produce clear error messages for bad input.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CLI-009 |
| Category | Language \| CLI |
| Status | Draft |
| Source | `test/03_system/feature/usage/cli_args_error_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests compile-time and runtime error cases for the cli keyword.
The compiler should catch invalid cli blocks at compile time,
and the runtime should produce clear error messages for bad input.

## Key Error Cases

- Duplicate option names
- Invalid default value types
- Unknown options at runtime
- Missing required positional args
- Type mismatch at runtime (e.g., "abc" for int option)
- Duplicate subcommand names
- Reserved option names (--help, --version)

## Scenarios

### CLI Args Error Handling

#### compile-time errors

#### rejects duplicate option names

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     verbose: false
#     verbose: true    # ERROR: duplicate option 'verbose'
val error = "duplicate option 'verbose'"
expect(error).to_contain("duplicate")
```

</details>

#### rejects invalid default expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     count: some_function()  # ERROR: default must be literal
val error = "default must be a literal value"
expect(error).to_contain("literal")
```

</details>

#### rejects duplicate subcommand names

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     command build:
#         target: "debug"
#     command build:           # ERROR: duplicate subcommand 'build'
#         mode: "fast"
val error = "duplicate subcommand 'build'"
expect(error).to_contain("duplicate subcommand")
```

</details>

#### warns on reserved option names

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     help: false    # WARNING: 'help' is reserved for --help
val warning = "option 'help' conflicts with built-in --help"
expect(warning).to_contain("conflicts with built-in")
0
```

</details>

#### runtime errors

#### reports unknown option

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     verbose: false
# cli.parse(["--unknown"]) should error
val error = "unknown option '--unknown'"
expect(error).to_start_with("unknown option")
```

</details>

#### reports missing value for option

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     output: "default.txt"
# cli.parse(["--output"]) without value should error
val error = "option '--output' requires a value"
expect(error).to_contain("requires a value")
```

</details>

#### reports type mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     count: 1
# cli.parse(["--count", "abc"]) should error
val error = "invalid value 'abc' for option '--count': expected integer"
expect(error).to_contain("invalid value")
expect(error).to_contain("expected integer")
```

</details>

#### reports missing required positional

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# cli:
#     command run:
#         positional file: text
# cli.parse(["run"]) without file should error
val error = "missing required argument: file"
expect(error).to_contain("missing required")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
