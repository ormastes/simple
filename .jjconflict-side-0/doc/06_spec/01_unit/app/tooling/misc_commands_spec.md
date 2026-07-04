# Miscellaneous Commands Specification

> Unit tests for miscellaneous command handling in the Simple language tooling. Validates common command-line parsing patterns including flag detection, argument validation, and conditional logic for various CLI utilities.

<!-- sdn-diagram:id=misc_commands_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=misc_commands_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

misc_commands_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=misc_commands_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Miscellaneous Commands Specification

Unit tests for miscellaneous command handling in the Simple language tooling. Validates common command-line parsing patterns including flag detection, argument validation, and conditional logic for various CLI utilities.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | Tooling-Misc |
| Category | Tooling |
| Status | In Progress |
| Source | `test/01_unit/app/tooling/misc_commands_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Unit tests for miscellaneous command handling in the Simple language tooling.
Validates common command-line parsing patterns including flag detection,
argument validation, and conditional logic for various CLI utilities.

## Test Coverage

- Help flag detection (-h, --help)
- Lock command flags (--check, --info)
- Argument length validation
- List slicing and indexing
- Option and Result type handling
- Conditional branching logic
- String interpolation
- Exit code conventions
- Boolean parameter handling

## Implementation Notes

Tests focus on fundamental command-line parsing operations and basic
language features used across multiple tooling commands.

## Scenarios

### help flag detection

#### detects -h flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "diagram", "-h"]
val has_help = args.any(_1 == "-h" or _1 == "--help")
expect has_help == true
```

</details>

#### detects --help flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "diagram", "--help"]
val has_help = args.any(_1 == "-h" or _1 == "--help")
expect has_help == true
```

</details>

#### no help when absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "diagram", "file.json"]
val has_help = args.any(_1 == "-h" or _1 == "--help")
expect has_help == false
```

</details>

### lock command flags

#### detects --check flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "lock", "--check"]
val check_only = args.any(_1 == "--check")
expect check_only == true
```

</details>

#### detects --info flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "lock", "--info"]
val info_only = args.any(_1 == "--info")
expect info_only == true
```

</details>

#### no flags when absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "lock"]
val check_only = args.any(_1 == "--check")
val info_only = args.any(_1 == "--info")
expect check_only == false
expect info_only == false
```

</details>

### argument length validation

#### run requires 2 args minimum

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "run", "script.spl"]
expect args.len() >= 2 == true
```

</details>

#### run fails with insufficient args

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

### list slicing

#### slices from index to end

1. expect diagram args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "diagram", "-f", "file.json"]
val diagram_args = args.slice(1, args.len())
expect diagram_args.len() == 3
```

</details>

#### empty slice when start equals end

1. expect diagram args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple"]
val diagram_args = args.slice(1, args.len())
expect diagram_args.len() == 0
```

</details>

### Option handling

#### Some wraps value

1. expect opt is some


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some("file.json")
expect opt.is_some() == true
```

</details>

#### unwrap gets value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some("file.json")
val value = opt.unwrap()
expect value == "file.json"
```

</details>

### conditional branches

#### info_only takes precedence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info_only = true
val check_only = true
val branch = if info_only: "info" elif check_only: "check" else: "generate"
expect branch == "info"
```

</details>

#### check_only when not info

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info_only = false
val check_only = true
val branch = if info_only: "info" elif check_only: "check" else: "generate"
expect branch == "check"
```

</details>

#### default when no flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val info_only = false
val check_only = false
val branch = if info_only: "info" elif check_only: "check" else: "generate"
expect branch == "generate"
```

</details>

### Result patterns

#### Ok unwraps value

1. expect Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect Ok(42).is_ok() == true
```

</details>

#### Err contains error

1. expect Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect Err("error").is_err() == true
```

</details>

### nested match patterns

#### outer match selects Some

1. Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outer = Some("value")
val selected = match outer:
    Some(v) => "has value"
    None => "no value"
expect selected == "has value"
```

</details>

#### checks None option

1. expect none outer is none


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val none_outer: Option<text> = None
expect none_outer.is_none() == true
```

</details>

### list length checks

#### detects non-empty patterns

1. expect patterns len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val patterns = ["*.spl", "*.txt"]
expect patterns.len() > 0 == true
```

</details>

#### list comparison works

1. expect test list len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val test_list = ["a", "b"]
expect test_list.len() == 2
```

</details>

### string formatting

#### interpolates variable

1. expect msg contains
2. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "test"
val events_count = 5
val msg = "Loaded profile: {name} ({events_count} events)"
expect msg.contains("test") == true
expect msg.contains("5") == true
```

</details>

#### interpolates path

1. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "output/diagram.puml"
val msg = "  Sequence diagram: {path}"
expect msg.contains("output/diagram.puml") == true
```

</details>

### exit code conventions

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

### boolean parameters

#### both gc flags false

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gc_log = false
val gc_off = false
expect gc_log == false
expect gc_off == false
```

</details>

#### gc_log true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gc_log = true
val gc_off = false
expect gc_log == true
```

</details>

#### gc_off true

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gc_log = false
val gc_off = true
expect gc_off == true
```

</details>

### early return pattern

#### validates condition for early return

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

#### continues when condition false

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

### misc_commands module compilation

#### compiles successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 + 1 == 2
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
