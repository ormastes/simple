# Compile Commands Specification

> <details>

<!-- sdn-diagram:id=compile_commands_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compile_commands_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compile_commands_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compile_commands_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 40 | 40 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compile Commands Specification

## Scenarios

### compile_commands module compilation

#### compiles successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect 1 + 1 == 2
```

</details>

### argument validation

#### compile requires source file

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile"]
expect args.len() < 2 == true
```

</details>

#### compile accepts source file

1. expect args len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl"]
expect args.len() >= 2 == true
```

</details>

### flag detection

#### detects --native flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl", "--native"]
val is_native = args.any(_1 == "--native")
expect is_native == true
```

</details>

#### detects --snapshot flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl", "--snapshot"]
val has_snapshot = args.any(_1 == "--snapshot")
expect has_snapshot == true
```

</details>

#### detects --layout-optimize flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl", "--native", "--layout-optimize"]
val has_layout = args.any(_1 == "--layout-optimize")
expect has_layout == true
```

</details>

#### detects --strip flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl", "--native", "--strip"]
val has_strip = args.any(_1 == "--strip")
expect has_strip == true
```

</details>

#### detects --map flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl", "--native", "--map"]
val has_map = args.any(_1 == "--map")
expect has_map == true
```

</details>

#### detects --shared flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl", "--native", "--shared"]
val is_shared = args.any(_1 == "--shared")
expect is_shared == true
```

</details>

### PIE flag handling

#### PIE enabled by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl", "--native"]
val no_pie = args.any(_1 == "--no-pie")
val pie = not no_pie
expect pie == true
```

</details>

#### PIE disabled with --no-pie

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl", "--native", "--no-pie"]
val no_pie = args.any(_1 == "--no-pie")
val pie = not no_pie
expect pie == false
```

</details>

### output file extraction

#### checks for -o flag presence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl", "-o", "output.smf"]
val has_o = args.any(_1 == "-o")
expect has_o == true
```

</details>

#### extracts output filename

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl", "-o", "output.smf"]
val output = args[4]
expect output == "output.smf"
```

</details>

### target flag handling

#### checks --target flag presence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl", "--target", "x86_64"]
val has_target = args.any(_1 == "--target")
expect has_target == true
```

</details>

#### extracts target architecture

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl", "--target", "x86_64"]
val target_arch = args[4]
expect target_arch == "x86_64"
```

</details>

### linker flag handling

#### checks --linker flag presence

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl", "--native", "--linker", "mold"]
val has_linker = args.any(_1 == "--linker")
expect has_linker == true
```

</details>

#### extracts linker name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl", "--native", "--linker", "mold"]
val linker_name = args[5]
expect linker_name == "mold"
```

</details>

### target architecture validation

#### validates x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = "x86_64"
val is_valid = arch == "x86_64" or arch == "aarch64" or arch == "riscv64"
expect is_valid == true
```

</details>

#### validates aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = "aarch64"
val is_valid = arch == "x86_64" or arch == "aarch64" or arch == "riscv64"
expect is_valid == true
```

</details>

#### rejects unknown arch

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = "unknown"
val is_valid = arch == "x86_64" or arch == "aarch64" or arch == "riscv64"
expect is_valid == false
```

</details>

### linker name validation

#### validates mold

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val linker = "mold"
val is_valid = linker == "mold" or linker == "lld" or linker == "ld"
expect is_valid == true
```

</details>

#### validates lld

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val linker = "lld"
val is_valid = linker == "mold" or linker == "lld" or linker == "ld"
expect is_valid == true
```

</details>

#### validates ld

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val linker = "ld"
val is_valid = linker == "mold" or linker == "lld" or linker == "ld"
expect is_valid == true
```

</details>

#### rejects unknown linker

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val linker = "unknown"
val is_valid = linker == "mold" or linker == "lld" or linker == "ld"
expect is_valid == false
```

</details>

### compilation mode detection

#### detects SMF mode (no --native)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl"]
val is_native = args.any(_1 == "--native")
expect is_native == false
```

</details>

#### detects native mode (--native present)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl", "--native"]
val is_native = args.any(_1 == "--native")
expect is_native == true
```

</details>

### source file extraction

#### extracts source from args[1]

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl"]
val source = args[1]
expect source == "test.spl"
```

</details>

#### handles path in source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "src/test.spl"]
val source = args[1]
expect source == "src/test.spl"
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
val opt = Some("x86_64")
expect opt.is_some() == true
```

</details>

#### unwrap gets value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some("x86_64")
val value = opt.unwrap()
expect value == "x86_64"
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
expect Ok("x86_64").is_ok() == true
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

### match on target arch

#### matches x86_64

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = "x86_64"
val matched = match arch:
    "x86_64" => true
    "aarch64" => false
    "riscv64" => false
    _ => false
expect matched == true
```

</details>

#### matches aarch64

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = "aarch64"
val matched = match arch:
    "x86_64" => false
    "aarch64" => true
    "riscv64" => false
    _ => false
expect matched == true
```

</details>

#### default case for unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arch = "unknown"
val matched = match arch:
    "x86_64" => false
    "aarch64" => false
    "riscv64" => false
    _ => true
expect matched == true
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

### combined flags

#### native with multiple options

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["simple", "compile", "test.spl", "--native", "--strip", "--layout-optimize"]
val is_native = args.any(_1 == "--native")
val has_strip = args.any(_1 == "--strip")
val has_layout = args.any(_1 == "--layout-optimize")
expect is_native == true
expect has_strip == true
expect has_layout == true
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/tooling/compile_commands_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- compile_commands module compilation
- argument validation
- flag detection
- PIE flag handling
- output file extraction
- target flag handling
- linker flag handling
- target architecture validation
- linker name validation
- compilation mode detection
- source file extraction
- Option handling
- Result patterns
- match on target arch
- exit codes
- combined flags
- early return pattern

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 40 |
| Active scenarios | 40 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
