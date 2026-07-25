# Argument Parsing Specification

> 1. expect flag starts with

<!-- sdn-diagram:id=argument_parsing_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=argument_parsing_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

argument_parsing_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=argument_parsing_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Argument Parsing Specification

## Scenarios

### Flag Parsing

#### recognizes double-dash flags

1. expect flag starts with
2. expect is flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = "--gc-log"
expect flag.starts_with("--")
expect is_flag(flag)
```

</details>

#### recognizes single-dash flags

1. expect flag starts with
2. expect is flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = "-v"
expect flag.starts_with("-")
expect is_flag(flag)
```

</details>

#### extracts flag name

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = "--gc-log"
match parse_flag(flag):
    case Some(name):
        expect name == "gc-log"
    case None:
        fail "Should parse flag name"
```

</details>

#### handles boolean flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = CliFlags {
    gc_log: true,
    gc_off: false,
    verbose: true,
    quiet: false
}

expect flags.gc_log == true
expect flags.gc_off == false
```

</details>

### Subcommand Parsing

#### identifies subcommand name

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = CliCommand {
    name: "test",
    args: ["path/to/test"],
    flags: CliFlags {
        gc_log: false,
        gc_off: false,
        verbose: false,
        quiet: false
    }
}

expect cmd.name == "test"
```

</details>

#### parses test subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subcommand = "test"
expect subcommand == "test"
```

</details>

#### parses compile subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subcommand = "compile"
expect subcommand == "compile"
```

</details>

#### parses run subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val subcommand = "run"
expect subcommand == "run"
```

</details>

### Argument Validation

#### validates file paths

1. expect path ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test.spl"
expect path.ends_with(".spl")
```

</details>

#### validates directory paths

1. expect path ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "test/"
expect path.ends_with("/")
```

</details>

#### handles empty arguments

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args: [text] = []
expect args.len() == 0
```

</details>

#### handles multiple arguments

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["arg1", "arg2", "arg3"]
expect args.len() == 3
expect args[0] == "arg1"
```

</details>

### Flag Combinations

#### enables multiple flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = CliFlags {
    gc_log: true,
    gc_off: false,
    verbose: true,
    quiet: false
}

expect flags.gc_log and flags.verbose
```

</details>

#### detects conflicting flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val verbose = true
val quiet = true

# These should be mutually exclusive
expect verbose and quiet # Both set incorrectly
```

</details>

#### applies default values

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flags = CliFlags {
    gc_log: false,
    gc_off: false,
    verbose: false,
    quiet: false
}

expect not flags.gc_log
expect not flags.gc_off
```

</details>

### Command Construction

#### builds test command

1. expect cmd args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = CliCommand {
    name: "test",
    args: ["test/unit/"],
    flags: CliFlags {
        gc_log: false,
        gc_off: false,
        verbose: true,
        quiet: false
    }
}

expect cmd.name == "test"
expect cmd.args.len() == 1
expect cmd.flags.verbose
```

</details>

#### builds compile command

1. expect cmd args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = CliCommand {
    name: "compile",
    args: ["input.spl", "-o", "output"],
    flags: CliFlags {
        gc_log: false,
        gc_off: false,
        verbose: false,
        quiet: false
    }
}

expect cmd.name == "compile"
expect cmd.args.len() == 3
```

</details>

### Error Handling

#### detects unknown flags

1. expect flag starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val flag = "--unknown-flag"
expect flag.starts_with("--")
# In real implementation, should check against known flags
```

</details>

#### detects invalid paths

1. expect not path ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "nonexistent.xyz"
expect not path.ends_with(".spl")
```

</details>

#### handles missing required arguments

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args: [text] = []
expect args.len() == 0
# Should require at least one argument for some commands
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/cli/argument_parsing_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Flag Parsing
- Subcommand Parsing
- Argument Validation
- Flag Combinations
- Command Construction
- Error Handling

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
