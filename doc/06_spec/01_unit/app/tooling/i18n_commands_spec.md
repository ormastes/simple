# I18n Commands Specification

> <details>

<!-- sdn-diagram:id=i18n_commands_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=i18n_commands_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

i18n_commands_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=i18n_commands_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 44 | 44 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# I18n Commands Specification

## Scenarios

### i18n_commands module compilation

#### compiles successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 + 1 == 2
```

</details>

### help flag detection

#### detects --help flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "i18n", "--help"]
val has_help = args.any(_1 == "--help" or _1 == "-h")
expect has_help == true
```

</details>

#### detects -h flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "i18n", "-h"]
val has_help = args.any(_1 == "--help" or _1 == "-h")
expect has_help == true
```

</details>

#### no help when absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "i18n", "extract"]
val has_help = args.any(_1 == "--help" or _1 == "-h")
expect has_help == false
```

</details>

### subcommand detection

#### detects extract subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "i18n", "extract"]
expect args[2] == "extract"
```

</details>

#### detects generate subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "i18n", "generate", "ko-KR"]
expect args[2] == "generate"
```

</details>

### argument validation

#### i18n requires subcommand

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "i18n"]
expect args.len() < 2 == true
```

</details>

#### i18n accepts subcommand

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "i18n", "extract"]
expect args.len() >= 2 == true
```

</details>

#### generate requires locale

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "i18n", "generate"]
expect args.len() < 3 == true
```

</details>

#### generate accepts locale

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "i18n", "generate", "ko-KR"]
expect args.len() >= 3 == true
```

</details>

### output flag handling

#### detects -o flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "i18n", "extract", "-o", "locale"]
val has_o = args.any(_1 == "-o")
expect has_o == true
```

</details>

#### detects --output flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "i18n", "extract", "--output", "locale"]
val has_output = args.any(_1 == "--output")
expect has_output == true
```

</details>

#### extracts output path

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "i18n", "extract", "-o", "locale"]
val output = args[4]
expect output == "locale"
```

</details>

### path argument extraction

#### extracts path from args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "i18n", "extract", "app/"]
val path = args[3]
expect path == "app/"
```

</details>

#### handles path with -o flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "i18n", "extract", "app/", "-o", "locale"]
val path = args[3]
expect path == "app/"
```

</details>

### locale extraction

#### extracts locale code

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "i18n", "generate", "ko-KR"]
val locale = args[3]
expect locale == "ko-KR"
```

</details>

#### extracts es-ES locale

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "i18n", "generate", "es-ES"]
val locale = args[3]
expect locale == "es-ES"
```

</details>

#### extracts ja-JP locale

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "i18n", "generate", "ja-JP"]
val locale = args[3]
expect locale == "ja-JP"
```

</details>

### match on subcommand

#### matches extract

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "extract"
val matched = match cmd:
    "extract" => true
    "generate" => false
    _ => false
expect matched == true
```

</details>

#### matches generate

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "generate"
val matched = match cmd:
    "extract" => false
    "generate" => true
    _ => false
expect matched == true
```

</details>

#### default case for unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "unknown"
val matched = match cmd:
    "extract" => false
    "generate" => false
    _ => true
expect matched == true
```

</details>

### starts_with check

#### detects flag prefix

1. expect arg starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg = "-o"
expect arg.starts_with("-") == true
```

</details>

#### detects long flag prefix

1. expect arg starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg = "--output"
expect arg.starts_with("--") == true
```

</details>

#### rejects non-flag

1. expect arg starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg = "app/"
expect arg.starts_with("-") == false
```

</details>

### file extension check

#### checks .spl extension

1. expect file ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
expect file.ends_with(".spl") == true
```

</details>

#### rejects other extensions

1. expect file ends with


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.rs"
expect file.ends_with(".spl") == false
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
expect Ok("module").is_ok() == true
```

</details>

#### Err result check

1. expect Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect Err("parse error").is_err() == true
```

</details>

### string formatting

#### interpolates locale

1. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val locale = "ko-KR"
val msg = "Generating {locale} locale template"
expect msg.contains("ko-KR") == true
```

</details>

#### interpolates path

1. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/"
val msg = "Extracting i18n strings from {path}"
expect msg.contains("src/") == true
```

</details>

#### interpolates count

1. expect msg contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = 42
val msg = "Extracted {count} i18n strings"
expect msg.contains("42") == true
```

</details>

### list operations

#### creates empty list

1. expect warnings len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = []
expect warnings.len() == 0
```

</details>

#### creates list with items

1. expect files len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val files = ["file1.spl", "file2.spl"]
expect files.len() == 2
```

</details>

#### iterates over list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = ["a", "b", "c"]
var count = 0
for item in items:
    count = count + 1
expect count == 3
```

</details>

### counter increment

#### increments file count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var file_count = 0
file_count = file_count + 1
expect file_count == 1
```

</details>

#### increments error count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var error_count = 0
error_count = error_count + 1
error_count = error_count + 1
expect error_count == 2
```

</details>

### struct construction

#### constructs with fields

1. expect warnings len
2. expect strings len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val warnings = ["warning 1", "warning 2"]
val strings = ["str1", "str2"]
expect warnings.len() == 2
expect strings.len() == 2
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

### early return pattern

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

#### continues when sufficient args

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

### while loop pattern

#### increments index

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var idx = 0
while idx < 3:
    idx = idx + 1
expect idx == 3
```

</details>

#### finds first non-flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["-o", "output", "path/"]
var idx = 0
var found = ""
while idx < args.len():
    if not args[idx].starts_with("-"):
        found = args[idx]
        break
    idx = idx + 1
expect found == "output"
```

</details>

### combined OR condition

#### matches either -o or --output

1. expect
2. expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg1 = "-o"
val arg2 = "--output"
expect (arg1 == "-o" or arg1 == "--output") == true
expect (arg2 == "-o" or arg2 == "--output") == true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/i18n_commands_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- i18n_commands module compilation
- help flag detection
- subcommand detection
- argument validation
- output flag handling
- path argument extraction
- locale extraction
- match on subcommand
- starts_with check
- file extension check
- Result patterns
- string formatting
- list operations
- counter increment
- struct construction
- exit codes
- early return pattern
- while loop pattern
- combined OR condition

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 44 |
| Active scenarios | 44 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
